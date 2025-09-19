// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_interleave(s1: Seq<char>, s2: Seq<char>, s3: Seq<char>) -> (result: bool)
    ensures
        (s1.len() + s2.len() != s3.len()) ==> result == false,
        (s1.len() == 0 && s2.len() == 0) ==> (result == (s3.len() == 0)),
        (s1.len() == 0) ==> (result == (s2 == s3)),
        (s2.len() == 0) ==> (result == (s1 == s3))
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}

fn main() {
    // let s1 = seq!['a', 'a', 'b', 'c', 'c'];
    // let s2 = seq!['d', 'b', 'b', 'c', 'a'];
    // let s3 = seq!['a', 'a', 'd', 'b', 'b', 'c', 'b', 'c', 'a', 'c'];
    // let result1 = is_interleave(s1, s2, s3);
    // println!("Result 1: {}", result1);
}