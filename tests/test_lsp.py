import json
import io
import os
import subprocess
import sys
import tempfile
import threading
import unittest

import kurt.kurt as kurt

from tests.utils import PROJECT_ROOT


class Client:
    # a minimal LSP client for `kurt --lsp`
    def __init__(self, cwd: str) -> None:
        self.process = subprocess.Popen([sys.executable, str(PROJECT_ROOT / 'src' / 'kurt' / 'kurt.py'), '--lsp'],
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd)
        self.next_id = 0

    def send(self, method: str, params: dict, request: bool = True) -> None:
        message = {'jsonrpc': '2.0', 'method': method, 'params': params}
        if request:
            self.next_id += 1
            message['id'] = self.next_id
        body = json.dumps(message).encode('utf-8')
        self.process.stdin.write(f'Content-Length: {len(body)}\r\n\r\n'.encode('ascii') + body)
        self.process.stdin.flush()

    def receive(self) -> dict:
        length = 0
        while True:
            line = self.process.stdout.readline().decode('ascii').strip()
            if not line:
                break
            if line.lower().startswith('content-length:'):
                length = int(line.split(':')[1])
        return json.loads(self.process.stdout.read(length))

    def request(self, method: str, params: dict) -> object:
        self.send(method, params)
        while True:
            message = self.receive()
            if message.get('id') == self.next_id:
                return message.get('result')

    def notification(self, method: str) -> dict:
        while True:
            message = self.receive()
            if message.get('method') == method:
                return message['params']

    def close(self) -> None:
        if self.process.poll() is None:
            self.process.kill()
        self.process.wait(timeout=10)
        self.process.stdin.close()
        self.process.stdout.close()
        self.process.stderr.close()


class TestLanguageServer(unittest.TestCase):
    def test_exit_without_shutdown_is_an_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            client = Client(tmp)
            try:
                client.request('initialize', {'processId': None, 'rootUri': None, 'capabilities': {}})
                client.send('exit', {}, request=False)
                self.assertEqual(client.process.wait(timeout=10), 1)
            finally:
                client.close()

    def test_protocol_position_and_uri_conversions(self):
        self.assertEqual(kurt.lsp_uri_path('file:///tmp/a%20b.kurt'), '/tmp/a b.kurt')
        self.assertEqual(kurt.lsp_uri_path('file://localhost/tmp/a.kurt'), '/tmp/a.kurt')
        self.assertEqual(kurt.lsp_uri_path('file:///C:/work/a.kurt'), 'C:/work/a.kurt')
        self.assertEqual(kurt.lsp_uri_path('untitled:test'), 'untitled:test')
        self.assertEqual(kurt.lsp_python_to_utf16('x😀y', 2), 3)
        self.assertEqual(kurt.lsp_utf16_to_python('x😀y', 3), 2)

    def test_initialization_options_and_close(self):
        with tempfile.TemporaryDirectory() as tmp:
            theories = os.path.join(tmp, 'theories')
            document = os.path.join(tmp, 'document')
            os.mkdir(theories)
            os.mkdir(document)
            with open(os.path.join(theories, 'extra.kurt'), 'w', encoding='utf-8') as stream:
                stream.write('bool Extra\nuse Extra "given"\n')
            uri = 'file://' + os.path.join(document, 'proof.kurt')
            client = Client(tmp)
            try:
                initialized = client.request('initialize', {
                    'processId': None,
                    'rootUri': None,
                    'capabilities': {},
                    'initializationOptions': {
                        'theoryPaths': [theories],
                        'checkOnType': True,
                        'checkOnChangeDelay': 0.05,
                    },
                })
                self.assertEqual(initialized['serverInfo']['name'], 'kurt')
                client.send('initialized', {}, request=False)
                text = 'load extra\nExtra\n'
                client.send('textDocument/didOpen', {'textDocument': {
                    'uri': uri, 'languageId': 'kurt', 'version': 1, 'text': text,
                }}, request=False)
                opened = client.notification('textDocument/publishDiagnostics')
                self.assertEqual(opened['version'], 1)
                self.assertEqual(opened['diagnostics'], [])

                # Type checking is debounced, versioned, and uses UTF-16 diagnostic columns.
                bad = 'load extra\n😀 Extra and Missing\n'
                client.send('textDocument/didChange', {
                    'textDocument': {'uri': uri, 'version': 2},
                    'contentChanges': [{'text': bad}],
                }, request=False)
                changed = client.notification('textDocument/publishDiagnostics')
                self.assertEqual(changed['version'], 2)
                self.assertEqual(changed['diagnostics'][0]['range']['end']['character'],
                                 len('😀 Extra and Missing'.encode('utf-16-le')) // 2)

                client.send('textDocument/didClose', {'textDocument': {'uri': uri}}, request=False)
                closed = client.notification('textDocument/publishDiagnostics')
                self.assertEqual(closed, {'uri': uri, 'diagnostics': [], 'version': 2})
                client.request('shutdown', {})
                client.send('exit', {}, request=False)
                self.assertEqual(client.process.wait(timeout=10), 0)
            finally:
                client.close()

    def test_unsaved_dependency_overlay_and_local_strictness(self):
        with tempfile.TemporaryDirectory() as tmp:
            dependency = os.path.join(tmp, 'dep.kurt')
            main = os.path.join(tmp, 'main.kurt')
            with open(dependency, 'w', encoding='utf-8') as stream:
                stream.write('bool DiskVersion\nuse DiskVersion "saved"\n')
            dependency_uri = 'file://' + dependency
            main_uri = 'file://' + main

            output = io.BytesIO()
            server = kurt.LanguageServer(io.BytesIO(), output)
            server.texts[dependency_uri] = 'bool EditorVersion\nuse EditorVersion "unsaved"\n'
            server.versions[dependency_uri] = 4
            server.texts[main_uri] = 'load dep\nEditorVersion\n'
            server.versions[main_uri] = 7
            server.check(main_uri)
            self.assertTrue(server.results[main_uri].ok, server.results[main_uri].error)

            # A document sibling is a source file, not a trusted `-p` theory. Strict checks may
            # search it, but must reject an unproved `use` in it.
            server.strict = True
            server.texts.pop(dependency_uri)
            server.versions.pop(dependency_uri)
            server.texts[main_uri] = 'load dep\nDiskVersion\n'
            server.versions[main_uri] = 8
            server.check(main_uri)
            self.assertFalse(server.results[main_uri].ok)
            self.assertIn('not allowed with `--strict`', server.results[main_uri].error or '')

            # Explicit extra paths are trusted only for files read from disk. Editing one makes
            # that in-memory text untrusted until it is saved.
            trusted = os.path.join(tmp, 'trusted')
            os.mkdir(trusted)
            trusted_dependency = os.path.join(trusted, 'teacher.kurt')
            with open(trusted_dependency, 'w', encoding='utf-8') as stream:
                stream.write('bool SavedAxiom\nuse SavedAxiom "teacher"\n')
            trusted_uri = 'file://' + trusted_dependency
            server.extra_paths = (trusted,)
            server.texts[trusted_uri] = 'bool UnsavedAxiom\nuse UnsavedAxiom "editing"\n'
            server.versions[trusted_uri] = 1
            server.texts[main_uri] = 'load teacher\nUnsavedAxiom\n'
            server.versions[main_uri] = 9
            server.check(main_uri)
            self.assertFalse(server.results[main_uri].ok)
            self.assertIn('not allowed with `--strict`', server.results[main_uri].error or '')

    def test_superseded_check_cannot_publish_or_replace_newer_result(self):
        uri = 'file:///tmp/proof.kurt'
        output = io.BytesIO()
        server = kurt.LanguageServer(io.BytesIO(), output)
        server.texts[uri] = 'old'
        server.versions[uri] = 1
        started = threading.Event()
        release = threading.Event()

        class ControlledSession:
            def check_text(self, text, name, **options):
                if text == 'old':
                    started.set()
                    release.wait(timeout=10)
                return kurt.CheckResult(text == 'new', '', None if text == 'new' else 'old error')

        server.session_for = lambda ignored_uri: ControlledSession()
        old = threading.Thread(target=server.check, args=(uri, 1))
        old.start()
        self.assertTrue(started.wait(timeout=10))
        with server.state_lock:
            server.texts[uri] = 'new'
            server.versions[uri] = 2
        release.set()
        old.join(timeout=10)
        self.assertFalse(old.is_alive())
        self.assertNotIn(uri, server.results)
        self.assertEqual(output.getvalue(), b'')

        server.check(uri, 2)
        self.assertTrue(server.results[uri].ok)

    def test_sibling_load_precedes_the_server_working_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            launch = os.path.join(tmp, 'launch')
            document = os.path.join(tmp, 'document')
            os.mkdir(launch)
            os.mkdir(document)
            def write(folder, name, text):
                path = os.path.join(folder, name)
                with open(path, 'w', encoding='utf-8') as stream:
                    stream.write(text)
                return path
            write(launch, 'dep.kurt', 'bool P\nuse P "given"\n')
            write(document, 'dep.kurt', 'bool P\nP "given"\n')
            text = 'load dep\nP\n'
            path = write(document, 'main.kurt', text)
            uri = 'file://' + path
            before = os.getcwd()
            try:
                os.chdir(launch)
                server = kurt.LanguageServer(io.BytesIO(), io.BytesIO())
                server.texts[uri] = text
                server.check(uri)
                self.assertFalse(server.results[uri].ok)
                self.assertEqual(server.results[uri].error, kurt.check_file(path).error)
                # Completion must use the same sibling source, not the launch directory's P.
                write(document, 'dep.kurt', 'bool DocumentFact\nuse DocumentFact "given"\n')
                server.texts[uri] = 'load dep\nDoc'
                items = server.completion({'textDocument': {'uri': uri},
                                           'position': {'line': 1, 'character': 3}})
                self.assertIn('DocumentFact', [item['label'] for item in items])
            finally:
                os.chdir(before)

    def test_a_proof_closed_without_qed_says_so_at_its_last_line(self):
        # (the end of the file, or a dedent, closes the proof: a derived line after its last one)
        for text in ('load prop\nbool A, B, C\nuse A\nuse A implies B\nshow B or C\nproof\n    B\n',
                     'load prop\nbool A, B, C\nuse A\nuse A implies B\nshow B or C\nproof\n    B\nA\n'):
            result = kurt.check_text(text, name='closing.kurt')
            self.assertTrue(result.ok, result.error)
            self.assertIn('; 7a by or-intro(7)', result.output)
            server = kurt.LanguageServer(io.BytesIO(), io.BytesIO())
            uri = 'file:///tmp/closing.kurt'
            server.texts[uri] = text
            server.check(uri)
            hints = server.inlay_hints({'textDocument': {'uri': uri},
                                        'range': {'start': {'line': 0, 'character': 0}, 'end': {'line': 10, 'character': 0}}})
            labels = {h['position']['line']: h['label'] for h in hints}
            self.assertEqual(labels[6], '  ; by 4(3); qed 7a by or-intro(7)')

    def test_the_protocol(self):
        with tempfile.TemporaryDirectory() as tmp:
            uri = 'file://' + os.path.join(tmp, 'proof.kurt')
            client = Client(tmp)
            try:
                capabilities = client.request('initialize', {'processId': None, 'rootUri': None, 'capabilities': {}})['capabilities']
                self.assertTrue(capabilities['hoverProvider'] and capabilities['inlayHintProvider'])
                client.send('initialized', {}, request=False)
                # an error: a diagnostic at its line
                bad = 'load prop\nbool A, B\nuse A\nB\n'
                client.send('textDocument/didOpen', {'textDocument': {'uri': uri, 'languageId': 'kurt', 'version': 1, 'text': bad}}, request=False)
                diagnostics = client.notification('textDocument/publishDiagnostics')['diagnostics']
                self.assertEqual(diagnostics[0]['range']['start']['line'], 3)
                self.assertIn('can not derive', diagnostics[0]['message'])
                self.assertEqual(diagnostics[0]['data']['failure']['kind'], 'not-derived')
                # fixed and saved: no diagnostics, the reasons as inlay hints and on hover
                good = 'load prop\nbool A, B\nuse A\nuse A implies B\nB\n'
                client.send('textDocument/didChange', {'textDocument': {'uri': uri, 'version': 2}, 'contentChanges': [{'text': good}]}, request=False)
                client.send('textDocument/didSave', {'textDocument': {'uri': uri}}, request=False)
                self.assertEqual(client.notification('textDocument/publishDiagnostics')['diagnostics'], [])
                hints = client.request('textDocument/inlayHint', {'textDocument': {'uri': uri},
                                       'range': {'start': {'line': 0, 'character': 0}, 'end': {'line': 10, 'character': 0}}})
                self.assertIn({'line': 4, 'character': 1}, [h['position'] for h in hints])
                labels = ' '.join(h['label'] for h in hints)
                self.assertIn('; by 4(3)', labels)                 # (the number is the line's own: left out)
                self.assertNotIn('5 by 4(3)', labels)
                hover = client.request('textDocument/hover', {'textDocument': {'uri': uri}, 'position': {'line': 4, 'character': 0}})
                self.assertIn('; by 4(3)', hover['contents']['value'])
                # ... with the certificate, whose places are links to the lines
                self.assertIn('**premise:**', hover['contents']['value'])
                self.assertRegex(hover['contents']['value'], r'\[line 3\]\(file://[^)]*#L3\)')
                # a line without a certificate says what it is
                axiom = client.request('textDocument/hover', {'textDocument': {'uri': uri}, 'position': {'line': 2, 'character': 0}})
                self.assertIn('**axiom:**', axiom['contents']['value'])
                # completion with the state at the cursor: in a proof, its goal
                text = 'load prop\nbool A, B\nuse A\nshow A or B\nproof\n    \n'
                client.send('textDocument/didChange', {'textDocument': {'uri': uri, 'version': 3}, 'contentChanges': [{'text': text}]}, request=False)
                items = client.request('textDocument/completion', {'textDocument': {'uri': uri}, 'position': {'line': 5, 'character': 4}})
                self.assertIn('A or B', [i['label'] for i in items])
                items = client.request('textDocument/completion', {'textDocument': {'uri': uri}, 'position': {'line': 0, 'character': 7}})
                self.assertEqual([i['label'] for i in items], ['prop'])      # after `load pr`: the theory
                client.request('shutdown', {})
                client.send('exit', {}, request=False)
                self.assertEqual(client.process.wait(timeout=10), 0)
            finally:
                client.close()


if __name__ == '__main__':
    unittest.main()
