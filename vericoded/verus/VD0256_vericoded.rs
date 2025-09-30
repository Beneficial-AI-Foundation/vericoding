use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max(a: &[i32], b: &[i32], i: usize, j: usize) -> (m: i32)
    requires 
        i < a.len(),
        j < b.len(),
    ensures 
        a[i as int] > b[j as int] ==> m == a[i as int],
        a[i as int] <= b[j as int] ==> m == b[j as int],
// </vc-spec>
// <vc-code>
{
    let ai = a[i];
    let bj = b[j];
    if ai > bj {
        ai
    } else {
        bj
    }
}
// </vc-code>

fn main() {}

}