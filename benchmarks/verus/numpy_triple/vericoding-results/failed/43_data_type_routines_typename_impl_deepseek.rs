// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix Seq::new parameters and indexing syntax */
fn type_to_seq(input: &str) -> Seq<char> {
    match input {
        "S1" => seq!['c','h','a','r','a','c','t','e','r'],
        "?" => seq!['b','o','o','l'],
        "B" => seq!['u','n','s','i','g','n','e','d',' ','c','h','a','r'],
        "D" => seq!['c','o','m','p','l','e','x',' ','d','o','u','b','l','e',' ','p','r','e','c','i','s','i','o','n'],
        "G" => seq!['c','o','m','p','l','e','x',' ','l','o','n','g',' ','d','o','u','b','l','e',' ','p','r','e','c','i','s','i','o','n'],
        "F" => seq!['c','o','m','p','l','e','x',' ','s','i','n','g','l','e',' ','p','r','e','c','i','s','i','o','n'],
        "I" => seq!['u','n','s','i','g','n','e','d',' ','i','n','t','e','g','e','r'],
        "H" => seq!['u','n','s','i','g','n','e','d',' ','s','h','o','r','t'],
        "L" => seq!['u','n','s','i','g','n','e','d',' ','l','o','n','g',' ','i','n','t','e','g','e','r'],
        "O" => seq!['o','b','j','e','c','t'],
        "Q" => seq!['u','n','s','i','g','n','e','d',' ','l','o','n','g',' ','l','o','n','g',' ','i','n','t','e','g','e','r'],
        "S" => seq!['c','h','a','r','a','c','t','e','r'],
        "U" => seq!['u','n','i','c','o','d','e'],
        "V" => seq!['v','o','i','d'],
        "b" => seq!['s','i','g','n','e','d',' ','c','h','a','r'],
        "d" => seq!['d','o','u','b','l','e',' ','p','r','e','c','i','s','i','o','n'],
        "g" => seq!['l','o','n','g',' ','p','r','e','c','i','s','i','o','n'],
        "f" => seq!['s','i','n','g','l','e',' ','p','r','e','c','i','s','i','o','n'],
        "i" => seq!['i','n','t','e','g','e','r'],
        "h" => seq!['s','h','o','r','t'],
        "l" => seq!['l','o','n','g',' ','i','n','t','e','g','e','r'],
        "q" => seq!['l','o','n','g',' ','l','o','n','g',' ','i','n','t','e','g','e','r'],
        _ => {
            let chars: Vec<char> = input.chars().collect();
            let len = chars.len();
            let mut seq_chars: Seq<char> = Seq::empty();
            let mut i: usize = 0;
            while i < len
                invariant
                    0 <= i <= len,
                    seq_chars.len() == i,
                    forall|j: int| 0 <= j < i ==> seq_chars[j] == chars[j as usize],
            {
                seq_chars = seq_chars.push(chars[i]);
                i += 1;
            }
            seq_chars
        }
    }
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
{
    /* code modified by LLM (iteration 5): fix type casts and indexing syntax */
    let seq_result = type_to_seq(char);
    let mut result_string = String::new();
    let len = seq_result.len();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            result_string@.len() == i,
            result_string@ =~= seq_result.subrange(0, i as int),
    {
        result_string.push(seq_result[i as int]);
        i += 1;
    }
    result_string
}
// </vc-code>


}
fn main() {}