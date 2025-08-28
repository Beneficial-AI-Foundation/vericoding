use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue was in the code syntax
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn max(a: &[i32], b: &[i32], i: usize, j: usize) -> (m: i32)
    requires 
        i < a.len(),
        j < b.len(),
    ensures 
        a[i as int] > b[j as int] ==> m == a[i as int],
        a[i as int] <= b[j as int] ==> m == b[j as int],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn max(a: &[i32], b: &[i32], i: usize, j: usize) -> (m: i32)
    requires
        i < a.len(),
        j < b.len(),
    ensures
        a[i as int] > b[j as int] ==> m == a[iI32(a[i as int]),
        a[i as int] <= b[j as int] ==> m == b[j as int]
{
    if a[i] > b[j] {
        a[i]
    } else {
        b[j]
    }
}
// </vc-code>

fn main() {}

}