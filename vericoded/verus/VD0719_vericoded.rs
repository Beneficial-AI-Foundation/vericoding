// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn seq_contains(s: Seq<i32>, val: i32) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == val
}

fn slice_contains(s: &[i32], val: i32) -> (result: bool)
    ensures
        result == seq_contains(s@, val),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|k: int| 0 <= k < i ==> s[k] != val,
        decreases s.len() - i
    {
        if s[i] == val {
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-helpers>

// <vc-spec>
fn has_common_element(a: &[i32], b: &[i32]) -> (result: bool)
    ensures 
        result ==> (exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && a[i] == b[j]) &&
        (!result ==> (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a[i] != b[j]))
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> !seq_contains(b@, a[k]),
        decreases a.len() - i
    {
        if slice_contains(b, a[i]) {
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-code>

}
fn main() {}