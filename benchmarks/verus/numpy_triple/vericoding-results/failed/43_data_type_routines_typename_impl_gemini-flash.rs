// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added `seq_to_string` helper to convert a `Seq<char>` to a `String`, and added a new helper `str_eq` to perform string equality comparison on `&str` types. Verus does not support direct `==` for `&str` by default. */
fn seq_to_string(s: Seq<char>) -> (res: String)
    ensures
        res@ == s,
{
    let mut result_vec = Vec_target::new();
    let mut i = 0;
    while i < s.len()
        invariant
            result_vec.len() == i,
            result_vec@.subsequence(0, i) == s.subsequence(0, i),
            i <= s.len(),
        decreases s.len() - i
    {
        result_vec.push(s[i]);
        i = i + 1;
    }
    String::from_vec(result_vec)
}

fn str_eq(a: &str, b: &str) -> (res: bool)
    ensures
        res == (a@ == b@),
{
    a@ == b@
}
// </vc-helpers>

// <vc-spec>
fn typename(char: &str) -> (result: String)
    ensures
        /* Known type code mappings from NumPy documentation */
        (char == "S1" ==> result@ == seq!['c','h','a','r','a','c','t','e','r']) &&
        (char == "?" ==> result@ == seq!['b','o','o','l']) &&
        (char == "B" ==> result@ == seq!['u','n','s','i','g','n','e','d',' ','c','h','a','r']) &&
        (char == "D" ==> result@ == seq!['c','o','m','p','l','e','x',' ','d','o','u','b','l','e',' ','p','r','e','c','i','s','i','o','n']) &&
        (char == "G" ==> result@ == seq!['c','o','m','p','l','e','x',' ','l','o','n','g',' ','d','o','u','b','l','e',' ','p','r','e','c','i','s','i','o','n']) &&
        (char == "F" ==> result@ == seq!['c','o','m','p','l','e','x',' ','s','i','n','g','l','e',' ','p','r','e','c','i','s','i','o','n']) &&
        (char == "I" ==> result@ == seq!['u','n','s','i','g','n','e','d',' ','i','n','t','e','g','e','r']) &&
        (char == "H" ==> result@ == seq!['u','n','s','i','g','n','e','d',' ','s','h','o','r','t']) &&
        (char == "L" ==> result@ == seq!['u','n','s','i','g','n','e','d',' ','l','o','n','g',' ','i','n','t','e','g','e','r']) &&
        (char == "O" ==> result@ == seq!['o','b','j','e','c','t']) &&
        (char == "Q" ==> result@ == seq!['u','n','s','i','g','n','e','d',' ','l','o','n','g',' ','l','o','n','g',' ','i','n','t','e','g','e','r']) &&
        (char == "S" ==> result@ == seq!['c','h','a','r','a','c','t','e','r']) &&
        (char == "U" ==> result@ == seq!['u','n','i','c','o','d','e']) &&
        (char == "V" ==> result@ == seq!['v','o','i','d']) &&
        (char == "b" ==> result@ == seq!['s','i','g','n','e','d',' ','c','h','a','r']) &&
        (char == "d" ==> result@ == seq!['d','o','u','b','l','e',' ','p','r','e','c','i','s','i','o','n']) &&
        (char == "g" ==> result@ == seq!['l','o','n','g',' ','p','r','e','c','i','s','i','o','n']) &&
        (char == "f" ==> result@ == seq!['s','i','n','g','l','e',' ','p','r','e','c','i','s','i','o','n']) &&
        (char == "i" ==> result@ == seq!['i','n','t','e','g','e','r']) &&
        (char == "h" ==> result@ == seq!['s','h','o','r','t']) &&
        (char == "l" ==> result@ == seq!['l','o','n','g',' ','i','n','t','e','g','e','r']) &&
        (char == "q" ==> result@ == seq!['l','o','n','g',' ','l','o','n','g',' ','i','n','t','e','g','e','r']) &&
        /* For unknown type codes, return default description */
        (char != "S1" && char != "?" && char != "B" && char != "D" && 
         char != "G" && char != "F" && char != "I" && char != "H" && 
         char != "L" && char != "O" && char != "Q" && char != "S" && 
         char != "U" && char != "V" && char != "b" && char != "d" && 
         char != "g" && char != "f" && char != "i" && char != "h" && 
         char != "l" && char != "q" ==>
         (result@ == seq!['u','n','k','n','o','w','n',' ','t','y','p','e'] || result@ == char@)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced direct string comparison (`char == "S1"`) with the `str_eq` helper function to satisfy Verus's requirements for string equality and fixed return values from `&str` literals to use `seq_to_string` for proper `String` creation. */
{
    if str_eq(char, "S1") { return seq_to_string(seq!['c','h','a','r','a','c','t','e','r']); }
    if str_eq(char, "?") { return seq_to_string(seq!['b','o','o','l']); }
    if str_eq(char, "B") { return seq_to_string(seq!['u','n','s','i','g','n','e','d',' ','c','h','a','r']); }
    if str_eq(char, "D") { return seq_to_string(seq!['c','o','m','p','l','e','x',' ','d','o','u','b','l','e',' ','p','r','e','c','i','s','i','o','n']); }
    if str_eq(char, "G") { return seq_to_string(seq!['c','o','m','p','l','e','x',' ','l','o','n','g',' ','d','o','u','b','l','e',' ','p','r','e','c','i','s','i','o','n']); }
    if str_eq(char, "F") { return seq_to_string(seq!['c','o','m','p','l','e','x',' ','s','i','n','g','l','e',' ','p','r','e','c','i','s','i','o','n']); }
    if str_eq(char, "I") { return seq_to_string(seq!['u','n','s','i','g','n','e','d',' ','i','n','t','e','g','e','r']); }
    if str_eq(char, "H") { return seq_to_string(seq!['u','n','s','i','g','n','e','d',' ','s','h','o','r','t']); }
    if str_eq(char, "L") { return seq_to_string(seq!['u','n','s','i','g','n','e','d',' ','l','o','n','g',' ','i','n','t','e','g','e','r']); }
    if str_eq(char, "O") { return seq_to_string(seq!['o','b','j','e','c','t']); }
    if str_eq(char, "Q") { return seq_to_string(seq!['u','n','s','i','g','n','e','d',' ','l','o','n','g',' ','l','o','n','g',' ','i','n','t','e','g','e','r']); }
    if str_eq(char, "S") { return seq_to_string(seq!['c','h','a','r','a','c','t','e','r']); }
    if str_eq(char, "U") { return seq_to_string(seq!['u','n','i','c','o','d','e']); }
    if str_eq(char, "V") { return seq_to_string(seq!['v','o','i','d']); }
    if str_eq(char, "b") { return seq_to_string(seq!['s','i','g','n','e','d',' ','c','h','a','r']); }
    if str_eq(char, "d") { return seq_to_string(seq!['d','o','u','b','l','e',' ','p','r','e','c','i','s','i','o','n']); }
    if str_eq(char, "g") { return seq_to_string(seq!['l','o','n','g',' ','p','r','e','c','i','s','i','o','n']); }
    if str_eq(char, "f") { return seq_to_string(seq!['s','i','n','g','l','e',' ','p','r','e','c','i','s','i','o','n']); }
    if str_eq(char, "i") { return seq_to_string(seq!['i','n','t','e','g','e','r']); }
    if str_eq(char, "h") { return seq_to_string(seq!['s','h','o','r','t']); }
    if str_eq(char, "l") { return seq_to_string(seq!['l','o','n','g',' ','i','n','t','e','g','e','r']); }
    if str_eq(char, "q") { return seq_to_string(seq!['l','o','n','g',' ','l','o','n','g',' ','i','n','t','e','g','e','r']); }

    seq_to_string(seq!['u','n','k','n','o','w','n',' ','t','y','p','e'])
}
// </vc-code>


}
fn main() {}