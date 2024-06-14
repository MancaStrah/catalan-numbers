--A ballot sequence is a sequence of votes in which the number of votes for one candidate (say A)
--is never less than the number of votes for another candidate (say B) at any point in the sequence.
--More formally, for any prefix of the sequence, the number of votes for candidate A must be at least
--the number of votes for candidate B.

--NOTE: the error in the file comes from the fact that we meed to prove "len - 1 < len"
--so lean knows that auxilary function (used in recursion) will terminate
--Right now we cant get rid of this error because there is no good documentation about "termination_by"
--and similar stuff
--The sequences generate_ballot_sequences n returns are otherwise correct

-- Define a function to check if a given ballot sequence is valid
def is_valid_ballot_sequence (seq : List Char) : Bool :=
  let rec aux : List Char → Nat → Nat → Bool
    | [], a_count, b_count => a_count >= b_count
    | (x :: xs), a_count, b_count =>
      if x = 'A' then
        aux xs (a_count + 1) b_count
      else if x = 'B' then
        if b_count + 1 > a_count then
          false
        else
          aux xs a_count (b_count + 1)
      else
        false
  aux seq 0 0

-- Define a function to generate all valid ballot sequences of length n
def generate_ballot_sequences (n : Nat) : List (List Char) :=
  let rec aux : Nat → Nat → Nat → List Char → List (List Char)
    | 0, _, _, seq => if is_valid_ballot_sequence seq then [seq] else []
    | len, a_count, b_count, seq =>
      let seqA := if a_count < n then aux (len - 1) (a_count + 1) b_count (seq ++ ['A']) else []
      let seqB := if b_count < a_count then aux (len - 1) a_count (b_count + 1) (seq ++ ['B']) else []
      seqA ++ seqB
  termination_by len a_count b_count seq => len
  aux n 0 0 []



-- Example usage
def main : IO Unit :=
  let sequences := generate_ballot_sequences 4
  sequences.forM (fun seq => IO.println (seq.asString))

#eval main
