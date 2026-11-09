"""Optional native build for wheels/editable installs.

Pure Python is the default. To request Cython extensions, install Cython in
this build environment, then set SUDOKU_BUILD_NATIVE=1. No silent fallback is
allowed when a native wheel was requested.
"""
from __future__ import annotations

import os
from setuptools import Extension, setup


def extension_modules():
    if os.environ.get("SUDOKU_BUILD_NATIVE", "0") != "1":
        return []
    try:
        from Cython.Build import cythonize
    except ImportError as exc:
        raise RuntimeError(
            "Native build requested but Cython is missing; install the [native] extra"
        ) from exc
    return cythonize(
        [Extension(name, [f"{name}.pyx"]) for name in
         ("native_ring", "native_sparse", "native_recursive")],
        compiler_directives={"language_level": 3},
    )


setup(ext_modules=extension_modules())
