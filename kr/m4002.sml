# Repo serialisation for HOL

(* Define the list structure: atoms (strings), NIL (empty string), or CONS cells *)
datatype list = NIL | Atom of string | Cons of list * list

(* Helper functions for LISP-like operations *)
fun car (Cons (x, _)) = x
  | car _ = raise Fail "car: not a Cons cell"

fun cdr (Cons (_, y)) = y
  | cdr _ = raise Fail "cdr: not a Cons cell"

fun cons (x, y) = Cons (x, y)

fun isAtom x = case x of Atom _ => true | _ => false

fun isList x = case x of NIL => true | Cons _ => true | _ => false

(* Write a list structure to a file in postfix format *)
fun writeToFile (lst, filename) =
    let
        val outStream = BinIO.openOut filename
        fun writeNullTerminated s =
            let
                (* Convert string to Word8Vector, adding null terminator *)
                val chars = explode s
                val bytes = Word8Vector.fromList (map (fn c => Word8.fromInt (ord c)) chars @ [0w0])
            in
                BinIO.output (outStream, bytes)
            end
        fun traverse NIL =
            writeNullTerminated "1" (* NIL: '1\0' *)
          | traverse (Atom s) =
            writeNullTerminated ("1" ^ s) (* Atom: '1<str>\0' *)
          | traverse (Cons (x, y)) =
            (traverse x; traverse y; writeNullTerminated "0") (* CONS: '0\0' *)
    in
        traverse lst;
        BinIO.closeOut outStream
    end
    handle e => (BinIO.closeOut outStream; raise e)

(* Read a postfix file and reconstruct the list structure *)
fun readFromFile filename =
    let
        val inStream = BinIO.openIn filename
        val stack = ref ([] : list list)
        fun readNullTerminated () =
            let
                fun readBytes acc =
                    case BinIO.input1 inStream of
                        NONE => if null acc then NONE else SOME (implode (rev acc))
                      | SOME w =>
                        if w = 0w0 then SOME (implode (rev acc))
                        else readBytes (chr (Word8.toInt w) :: acc)
            in
                readBytes []
            end
        fun process () =
            case readNullTerminated () of
                NONE => () (* EOF *)
              | SOME "0" => (* CONS *)
                (case !stack of
                     y :: x :: rest =>
                     (stack := cons (x, y) :: rest; process ())
                   | _ => raise Fail "Not enough elements on stack for CONS")
              | SOME s =>
                if String.isPrefix "1" s then
                    let val atom = String.extract (s, 1, NONE) in
                        stack := (if atom = "" then NIL else Atom atom) :: !stack;
                        process ()
                    end
                else
                    raise Fail ("Invalid string: " ^ s)
    in
        process ();
        BinIO.closeIn inStream;
        case !stack of
            [result] => result
          | _ => raise Fail ("Invalid file format: stack should have one element, got " ^
                            Int.toString (length (!stack)))
    end
    handle e => (BinIO.closeIn inStream; raise e)

(* Print the list for verification *)
fun printList NIL = "NIL"
  | printList (Atom s) = s
  | printList (Cons (x, y)) =
    let
        fun printCdr NIL = ""
          | printCdr (Atom s) = s
          | printCdr (Cons (a, b)) = printList a ^ " . " ^ printCdr b
    in
        "(" ^ printList x ^ " . " ^ printCdr y ^ ")"
    end

(* Example usage *)
val testList = cons (Atom "a", cons (Atom "b", NIL))
val _ = writeToFile (testList, "list.bin")
val reconstructed = readFromFile "list.bin"
val _ = print ("Original list: " ^ printList testList ^ "\n")
val _ = print ("Reconstructed list: " ^ printList reconstructed ^ "\n")