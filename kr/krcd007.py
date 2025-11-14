from krcd006 import SPADEIORepository

# Writing a new repo from scratch (e.g., SML export simulation)
repo = SPADEIORepository('example.spade')
repo.open_write()
repo.write_sequence(b"Theory: Basics")  # Returns (18, 1)  # len(b'Theory: Basics\x00')=18
repo.write_sequence("Axiom: commute")   # Auto-encodes str; returns updated pos/count
repo.write_sequence(bytearray(b"Proof: ..."))  # From mutable
print(repo.file_pos, repo.seq_count)  # e.g., 50, 3
repo.close()

# Reading into structured list (efficient for large repos)
repo = SPADEIORepository('example.spade')
with repo as r:  # Auto-open/close
    all_seqs = r.read_all()  # Dynamic list: [b'Theory: Basics', b'Axiom: commute', b'Proof: ...']
    print(len(all_seqs))  # 3
    print(all_seqs[1])    # b'Axiom: commute'  # O(1) index via refs

# Streaming read (for huge files, avoid full load)
repo.open_read()
seq, pos, count = repo.read_sequence()  # Process one-by-one
# ... loop until EOFError
repo.close()

# Append after read (spec-compliant)
repo.open_read()
try:
    while True:
        repo.read_sequence()
except EOFError:
    pass  # Now at EOF
repo.open_append()
repo.write_sequence(b"New Axiom")
repo.close()
