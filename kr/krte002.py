import os
import tempfile
import shutil
import sys

# Ensure we can import from kr
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from kr.krcd009 import LowLevelIO, SExpressions  # noqa: E402


def test_integration():
    print("Starting Integration Test (Direct KR)...")

    # Setup temp dir for repo
    temp_dir = tempfile.mkdtemp()
    repo_path = os.path.join(temp_dir, "integration_test.spade")
    print(f"Using temporary repo path: {repo_path}")

    try:
        # 1. Create Repository
        print("-> Creating Repository")
        io = LowLevelIO()
        io.open_new_repository(repo_path, version=1)
        io.close_repository()

        if not os.path.exists(repo_path):
            raise Exception("Repository file was not created!")
        print("<- Repository created")

        # 2. Write S-Expression
        # Write ["Hello", "World"] -> (Hello . (World . Nil))
        # In bytes: [b"Hello", b"World"]
        print("-> Writing S-Expression")

        io = LowLevelIO()
        io.open_existing_repository_read(repo_path)
        io.open_existing_repository_append(repo_path)

        sexp = SExpressions(io)
        data_to_write = [b"Hello", b"World"]
        seq_num = sexp.write_recursive(data_to_write)

        io.close_repository()
        print(f"<- Wrote S-Expression. Sequence Number: {seq_num}")

        # 3. Read S-Expression
        print("-> Reading S-Expression")
        io = LowLevelIO()
        io.open_existing_repository_read(repo_path)

        sexp = SExpressions(io)
        val = sexp.read_recursive(seq_num)

        io.close_repository()
        print(f"<- Read S-Expression: {val}")

        # 4. Verify
        # Expected: (b"Hello", (b"World", None))
        expected = (b"Hello", (b"World", None))

        if val != expected:
            raise Exception(f"Read mismatch! Expected {expected}, got {val}")

        print("SUCCESS: All integration steps passed.")

    except Exception as e:
        print(f"FAILED: {e}")
        raise
    finally:
        shutil.rmtree(temp_dir)


if __name__ == "__main__":
    test_integration()
