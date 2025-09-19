// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_subsequence(s: Vec<u8>, t: Vec<u8>) -> (result: bool)
    ensures
        s.len() == 0 ==> result == true,
        s@ == t@ ==> result == true,
        s.len() > t.len() ==> result == false,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>

/* Apps difficulty: interview
   Assurance level: unguarded */

}

fn main() {
    // let s1 = "abc".as_bytes().to_vec();
    // let t1 = "ahbgdc".as_bytes().to_vec();
    // println!("{}", is_subsequence(s1, t1));
    // 
    // let s2 = "axc".as_bytes().to_vec();
    // let t2 = "ahbgdc".as_bytes().to_vec();
    // println!("{}", is_subsequence(s2, t2));
    // 
    // let s3 = "".as_bytes().to_vec();
    // let t3 = "ahbgdc".as_bytes().to_vec();
    // println!("{}", is_subsequence(s3, t3));
}