import json
import io
import os
import subprocess
import sys
import tempfile
import unittest

import kurt.kurt as kurt

from tests.utils import PROJECT_ROOT


class Client:
    # a minimal LSP client for `kurt --lsp`
    def __init__(self, cwd: str) -> None:
        self.process = subprocess.Popen([sys.executable, str(PROJECT_ROOT / 'src' / 'kurt' / 'kurt.py'), '--lsp'],
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE, cwd=cwd)
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


class TestLanguageServer(unittest.TestCase):
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
                # fixed and saved: no diagnostics, the reasons as inlay hints and on hover
                good = 'load prop\nbool A, B\nuse A\nuse A implies B\nB\n'
                client.send('textDocument/didChange', {'textDocument': {'uri': uri, 'version': 2}, 'contentChanges': [{'text': good}]}, request=False)
                client.send('textDocument/didSave', {'textDocument': {'uri': uri}}, request=False)
                self.assertEqual(client.notification('textDocument/publishDiagnostics')['diagnostics'], [])
                hints = client.request('textDocument/inlayHint', {'textDocument': {'uri': uri},
                                       'range': {'start': {'line': 0, 'character': 0}, 'end': {'line': 10, 'character': 0}}})
                self.assertIn({'line': 4, 'character': 1}, [h['position'] for h in hints])
                self.assertIn('5 by 4(3)', ' '.join(h['label'] for h in hints))
                hover = client.request('textDocument/hover', {'textDocument': {'uri': uri}, 'position': {'line': 4, 'character': 0}})
                self.assertIn('5 by 4(3)', hover['contents']['value'])
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
                if client.process.poll() is None:
                    client.process.kill()


if __name__ == '__main__':
    unittest.main()
