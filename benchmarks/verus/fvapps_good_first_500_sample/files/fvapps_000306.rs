// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_substrings_ones(s: Vec<char>) -> (result: u32)
    requires 
        s.len() > 0,
        s.len() <= 100000,
        forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1'),
    ensures 
        result < 1000000007,
        (s.len() == 0 || (forall|c: char| s@.contains(c) ==> c == '0')) ==> result == 0,
        (forall|c: char| s@.contains(c) ==> c == '1') ==> result == ((s.len() * (s.len() + 1) / 2) % 1000000007) as u32,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0u32
    // impl-end
}
// </vc-code>


}
fn main() {
    // let test1 = vec!['0', '1', '1', '0', '1', '1', '1'];
    // let result1 = count_substrings_ones(test1);
    // println!("Result for '0110111': {}", result1);
    
    // let test2 = vec!['1', '0', '1'];
    // let result2 = count_substrings_ones(test2);
    // println!("Result for '101': {}", result2);
    
    // let test3 = vec!['1', '1', '1', '1', '1', '1'];
    // let result3 = count_substrings_ones(test3);
    // println!("Result for '111111': {}", result3);
}