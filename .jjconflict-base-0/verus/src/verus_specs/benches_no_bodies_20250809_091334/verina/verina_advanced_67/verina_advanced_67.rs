use vstd::prelude::*;

verus! {

// Helper function to create a repeated character sequence
spec fn repeat_char(ch: char, n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq![]
    } else {
        seq![ch] + repeat_char(ch, (n - 1) as nat)
    }
}

// Helper function to decode RLE for postcondition
spec fn decode_rle(lst: Seq<(char, u32)>) -> Seq<char>
    decreases lst.len()
{
    if lst.len() == 0 {
        seq![]
    } else {
        let (ch, cnt) = lst[0];
        repeat_char(ch, cnt as nat) + decode_rle(lst.subrange(1, lst.len() as int))
    }
}

// Precondition (trivially true in this case)
spec fn run_length_encode_precond(s: Seq<char>) -> bool {
    true
}

// Postcondition matching the original Lean specification
spec fn run_length_encode_postcond(s: Seq<char>, result: Seq<(char, u32)>) -> bool {
    // All counts are positive
    (forall|i: int| 0 <= i < result.len() ==> (#[trigger] result.index(i)).1 > 0) &&
    // Adjacent pairs have different characters (simplified to avoid trigger issues)
    (result.len() <= 1 || (forall|i: int| 0 <= i < result.len() - 1 ==> 
        result.index(i).0 != result.index(add(i, 1)).0)) &&
    // Decoding gives back original string
    decode_rle(result) == s
}

// Helper function to decode RLE (executable version)
fn decode_rle_exec(lst: Vec<(char, u32)>) -> Vec<char> {
    return Vec::new();  // TODO: Remove this line and implement the function body
}

// Main run-length encode function
fn run_length_encode(s: Vec<char>) -> (result: Vec<(char, u32)>)
    requires run_length_encode_precond(s@)
    ensures run_length_encode_postcond(s@, result@)
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

fn main() {
    // TODO: Remove this comment and implement the function body
}

} // verus!