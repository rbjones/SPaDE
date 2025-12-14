"""
Integration test for the SML-backed repository implementation.
Uses LowLevelIOSML and SExpressionsSML (krcd012.py) to ensure parity with
krcd009.py integration behaviour.
"""

import os
import shutil
import sys
import tempfile

import pytest

# Skip if ProofPower/pp is unavailable; the SML-backed wrapper needs it.
if shutil.which("pp") is None:
    pytest.skip("ProofPower 'pp' not found in PATH", allow_module_level=True)

# Ensure we can import from kr
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from kr.krcd012 import LowLevelIOSML, SExpressionsSML  # noqa: E402


def test_integration_sml():
    print("Starting Integration Test (SML KR)...")

    temp_dir = tempfile.mkdtemp()
    repo_path = os.path.join(temp_dir, "integration_test_sml.spade")
    print(f"Using temporary repo path: {repo_path}")

    try:
        # 1. Create repository via SML backend
        print("-> Creating Repository")
        io = LowLevelIOSML()
        io.open_new_repository(repo_path, version=1)
        io.close_repository()
        assert os.path.exists(repo_path), "Repository file was not created"
        print("<- Repository created")

        # 2. Write S-expression ["Hello", "World"] -> (Hello . (World . Nil))
        print("-> Writing S-Expression")
        io = LowLevelIOSML()
        io.open_existing_repository_read(repo_path)
        io.open_existing_repository_append(repo_path)

        sexp = SExpressionsSML(io)
        data_to_write = [b"Hello", b"World"]
        seq_num = sexp.write_recursive(data_to_write)
        io.close_repository()
        print(f"<- Wrote S-Expression. Sequence Number: {seq_num}")

        # 3. Read S-expression back
        print("-> Reading S-Expression")
        io = LowLevelIOSML()
        io.open_existing_repository_read(repo_path)

        sexp = SExpressionsSML(io)
        val = sexp.read_recursive(seq_num)
        io.close_repository()
        print(f"<- Read S-Expression: {val}")

        # 4. Verify
        expected = (b"Hello", (b"World", None))
        assert val == expected, f"Read mismatch! Expected {expected}, got {val}"

        print("SUCCESS: All SML integration steps passed.")
    finally:
        shutil.rmtree(temp_dir)


if __name__ == "__main__":
    test_integration_sml()
