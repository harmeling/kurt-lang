# utils.py
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[1]

import contextlib

@contextlib.contextmanager
def kernel_checking():
    # every step the search accepts is checked again by the kernel (`kurt.kurt.kernel_check`);
    # a step the kernel rejects raises `KernelError`, which fails the test
    import kurt.kurt as kurt_module
    old = kurt_module.kernel_check
    kurt_module.kernel_check = True
    try:
        yield
    finally:
        kurt_module.kernel_check = old
        kurt_module.certificates.clear()
