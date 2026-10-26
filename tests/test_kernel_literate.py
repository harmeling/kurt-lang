import importlib.util
import unittest
from pathlib import Path

from tests.utils import PROJECT_ROOT

# doc/kurt-kernel-code.md cites the kernel's code chunk by chunk (a literate document, 2026-10-16);
# scripts/kernel_doc.py takes the chunks from kurt.py. A chunk that no longer is the code fails
# here: change the kernel, then `python3 scripts/kernel_doc.py --update`, and read the prose again.

spec = importlib.util.spec_from_file_location('kernel_doc', PROJECT_ROOT / 'scripts' / 'kernel_doc.py')
assert spec is not None and spec.loader is not None
kernel_doc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(kernel_doc)


class TestKernelLiterate(unittest.TestCase):
    def test_every_chunk_is_the_code(self):
        stale = kernel_doc.process(kernel_doc.DOCUMENT, update=False)
        self.assertEqual(stale, [], 'doc/kurt-kernel-code.md cites code that changed: python3 scripts/kernel_doc.py --update, then read the prose again')

    def test_the_document_cites_the_whole_kernel(self):
        # every `k_*` function, `kernel_verify`, `kernel_verify_block`, `Certificate`, `KernelEnv`
        # and `record_certificate` are cited (a new kernel function needs its paragraph)
        text = kernel_doc.DOCUMENT.read_text(encoding='utf-8')
        source = kernel_doc.SOURCE.read_text(encoding='utf-8').split('\n')
        names = [m.group(1) for line in source for m in [kernel_doc.re.match(r'def (k_\w+|kernel_\w+|record_certificate)\(', line)] if m]
        names += ['Certificate', 'KernelEnv', 'KernelError', 'KernelReject']
        missing = [n for n in names if f'<!-- cite: def {n}' not in text and f'<!-- cite: class {n}' not in text
                   and f'<!-- cite: {n} ::' not in text]
        self.assertEqual(missing, [], f'not cited in doc/kurt-kernel-code.md: {missing}')

    def test_a_stale_chunk_is_found(self):
        # the tool itself: a copy of the document with one chunk changed is reported
        import tempfile
        text = kernel_doc.DOCUMENT.read_text(encoding='utf-8')
        marker = '<!-- cite: def k_rename -->\n```python\n'
        self.assertIn(marker, text)
        changed = text.replace(marker, marker + '# a line that is not in kurt.py\n', 1)
        with tempfile.NamedTemporaryFile('w', suffix='.md', delete=False, encoding='utf-8') as f:
            f.write(changed)
        try:
            stale = kernel_doc.process(Path(f.name), update=False)
        finally:
            Path(f.name).unlink()
        self.assertEqual(stale, ['def k_rename'])


if __name__ == '__main__':
    unittest.main()
