use vstd::prelude::*;

verus! {

spec fn is_space_comma_dot(c: char) -> bool {
    c == ' ' || c == ',' || c == '.'
}

// <vc-helpers>
fn char_to_string(c: char) -> String {
    let mut s = String::new();
    s.push(c);
    s
}
// </vc-helpers>

// <vc-spec>
fn replace_with_colon(s: &str) -> (v: String)
    ensures 
        v@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> {
            if is_space_comma_dot(s@[i]) {
                v@[i] == ':'
            } else {
                v@[i] == s@[i]
            }
        }
// </vc-spec>
// <vc-code>
{
    let mut result_string = String::new();
    let s_spec = s.bytes().map(|b| b as char).collect::<Vec<char>>(); // Get the spec-level sequence of chars

    // We keep track of the result string's spec representation as we build it.
    // The invariant ensures that `result_string_spec` always matches its runtime content.
    // We also use it to build the postcondition.
    let mut result_string_spec = Seq::<char>::empty();

    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result_string.len() == i,
            result_string_spec.len() == i,
            forall|j: int| 0 <= j < i ==> {
                if is_space_comma_dot(s_spec.seq_as_vec()@[j]) {
                    result_string_spec@[j] == ':'
                } else {
                    result_string_spec@[j] == s_spec.seq_as_vec()@[j]
                }
            },
            result_string@ == result_string_spec,
    {
        let c = s.as_bytes()[i] as char; // Get the char at index i

        if is_space_comma_dot(c) {
            result_string.push(':');
            result_string_spec = result_string_spec.push(':');
        } else {
            result_string.push(c);
            result_string_spec = result_string_spec.push(c);
        }
        i = i + 1;
    }

    // Post-condition proofs
    assert(result_string@.len() == s_spec.seq_as_vec().len());
    assert(result_string@ == result_string_spec);
    assert(result_string.len() == s.len());


    result_string
}
// </vc-code>

fn main() {}

}