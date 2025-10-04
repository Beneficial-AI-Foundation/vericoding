// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn distinct_subseq_count(s: Vec<u8>) -> (result: u32)
    requires 
        s.len() > 0,
        s.len() <= 2000,
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 97 && s[i] <= 122,
    ensures 
        result < 1000000007,
        result >= s.len() as u32,
        (forall|i: int| 0 <= i < s.len() ==> s[i] == 97) ==> result == s.len() as u32,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // let s1 = vec![97, 98, 99]; // "abc"
    // let result1 = distinct_subseq_count(s1);
    // assert(result1 == 7);
    
    // let s2 = vec![97, 98, 97]; // "aba"
    // let result2 = distinct_subseq_count(s2);
    // assert(result2 == 6);
    
    // let s3 = vec![97, 97, 97]; // "aaa"
    // let result3 = distinct_subseq_count(s3);
    // assert(result3 == 3);
}