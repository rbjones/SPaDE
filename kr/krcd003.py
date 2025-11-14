# Repository read and write


class Cons:
    def __init__(self, car, cdr):
        self.car = car
        self.cdr = cdr

    def __repr__(self):
        def print_list(lst, first=True):
            if lst == "":
                return "NIL" if first else ""
            if not isinstance(lst, Cons):
                return str(lst)
            if lst.cdr == "":
                return f"({lst.car})" if first else str(lst.car)
            part1 = print_list(lst.car, True)
            part2 = print_list(lst.cdr, False)
            return f"({' ' if first else ''}{part1} . {part2})"

        return print_list(self)


# Helper functions for LISP-like operations
def cons(car, cdr):
    return Cons(car, cdr)


def car(lst):
    return lst.car if isinstance(lst, Cons) else None


def cdr(lst):
    return lst.cdr if isinstance(lst, Cons) else None


def is_atom(x):
    return x is not None and x != "" and not isinstance(x, Cons)


def is_list(x):
    return x == "" or isinstance(x, Cons)


def write_to_file(lst, filename, debug=False):
    """
    Write a LISP-like list structure to a file in postfix format.
    - Atoms: '1' + string + null terminator (e.g., '1abc\0').
    - NIL: '1\0' (empty string after '1').
    - CONS: '0\0' (ASCII '0' followed by null terminator).
    """
    with open(filename, 'wb') as f:
        def traverse(lst):
            if lst == "":
                f.write(b"1\0")  # NIL
                if debug:
                    print("Wrote NIL: b'1\\0'")
            elif is_atom(lst):
                f.write(f"1{lst}\0".encode('utf-8'))  # Atom
                if debug:
                    print(f"Wrote atom: b'1{lst}\\0'")
            elif isinstance(lst, Cons):
                traverse(lst.car)  # Write car first
                traverse(lst.cdr)  # Then cdr
                f.write(b"0\0")  # Then CONS
                if debug:
                    print("Wrote CONS: b'0\\0'")
            else:
                raise ValueError(f"Invalid list element: {lst}")

        traverse(lst)


def read_from_file(filename, debug=False):
    """
    Read a postfix file and reconstruct the list structure using a stack.
    - Reads null-terminated strings.
    - '0\0': Pop top two stack elements, create CONS (top as cdr, second as car).
    - '1...': Push atom (string after '1', empty for NIL).
    Returns the top of the stack (the reconstructed list).
    """
    stack = []
    with open(filename, 'rb') as f:
        buffer = b""
        while True:
            byte = f.read(1)
            if not byte:  # EOF
                if buffer:
                    raise ValueError(f"Incomplete string at EOF: {buffer}")
                break
            if byte == b"\0":  # Null terminator
                if not buffer:
                    raise ValueError("Empty string in file")
                if buffer == b"0":  # CONS (ASCII '0')
                    if len(stack) < 2:
                        raise ValueError("Not enough elements on stack for CONS")
                    # Pop top as cdr, second as car
                    cdr = stack.pop()
                    car = stack.pop()
                    stack.append(cons(car, cdr))
                    if debug:
                        print(f"CONS: Created ({car} . {cdr}), Stack: {stack}")
                elif buffer.startswith(b"1"):  # Atom or NIL
                    # Extract string after '1' (empty for NIL)
                    atom = buffer[1:].decode('utf-8')
                    stack.append(atom)
                    if debug:
                        print(f"Pushed atom/NIL: {atom!r}, Stack: {stack}")
                else:
                    raise ValueError(f"Invalid string: {buffer.decode('utf-8', errors='replace')}")
                buffer = b""
            else:
                buffer += byte

    if len(stack) != 1:
        raise ValueError(f"Invalid file format: "
                         f"stack should have one element, got {len(stack)}")
    return stack[0]


# Example usage
if __name__ == "__main__":
    # Create a list: (a . (b . NIL))
    lst = cons("a", cons("b", ""))

    # Write to file with debug output
    print(f"Original list: {lst}")
    write_to_file(lst, "list.txt", debug=True)

    # Read from file with debug output
    reconstructed = read_from_file("list.txt", debug=True)
    print(f"Reconstructed list: {reconstructed}")
