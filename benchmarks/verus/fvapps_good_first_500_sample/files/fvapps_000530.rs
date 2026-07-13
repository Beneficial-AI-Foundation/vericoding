// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_valid_letter(c: char) -> bool {
    c == 'a' || c == 'b' || c == 'c' || c == 'd' ||
    c == 'e' || c == 'f' || c == 'g' || c == 'h' ||
    c == 'i' || c == 'j' || c == 'k' || c == 'l' ||
    c == 'm' || c == 'n' || c == 'o' || c == 'p'
}

spec fn is_binary_char(c: char) -> bool {
    c == '0' || c == '1'
}

fn decode_binary_string(s: Vec<char>) -> (result: Vec<char>)
    requires 
        s.len() % 4 == 0,
        forall|i: int| 0 <= i < s.len() ==> is_binary_char(s[i]),
    ensures
        result.len() == s.len() / 4,
        forall|i: int| 0 <= i < result.len() ==> is_valid_letter(result[i])
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


}
fn main() {
    // let test1 = vec!['0', '0', '0', '0'];
    // let result1 = decode_binary_string(test1);
    // println!("{:?}", result1);
    //
    // let test2 = vec!['0', '0', '0', '0', '1', '1', '1', '1'];
    // let result2 = decode_binary_string(test2);
    // println!("{:?}", result2);
    //
    // let test3 = vec!['1', '0', '0', '1'];
    // let result3 = decode_binary_string(test3);
    // println!("{:?}", result3);
}