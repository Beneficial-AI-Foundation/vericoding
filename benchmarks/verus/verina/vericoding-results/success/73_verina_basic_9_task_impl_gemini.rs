// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn contains(v: &Vec<i32>, x: i32) -> (result: bool)
    ensures result == v@.contains(x),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|k: int| 0 <= k < (i as int) ==> v[k] != x,
        decreases v.len() - i
    {
        if v[i] == x {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn has_common_element(a: &Vec<i32>, b: &Vec<i32>) -> (result: bool)
    requires 
        a.len() > 0,
        b.len() > 0,
    ensures
        result == (exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j]),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < (i as int) ==> !b@.contains(a[k]),
        decreases a.len() - i
    {
        if contains(b, a[i]) {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}