// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn remove_element(s: &Vec<i32>, k: usize) -> (v: Vec<i32>)
    requires 
        k < s.len(),
    ensures
        v.len() == s.len() - 1,
        forall|i: int| 0 <= i < k ==> v[i] == s[i],
        forall|i: int| k <= i < v.len() ==> v[i] == s[(i + 1) as int],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}