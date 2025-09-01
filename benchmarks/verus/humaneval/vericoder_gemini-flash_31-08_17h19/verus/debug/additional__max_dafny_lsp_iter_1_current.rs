use vstd::prelude::*;

verus! {

// <vc-helpers>
fn max_val_in_slice(a: &[i32]) -> (max_val: i32)
    requires a.len() > 0
    ensures forall|k: int| 0 <= k < a.len() ==> a[k] <= max_val
{
    let mut max_so_far = a[0];
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] <= max_so_far
    {
        if a[i] > max_so_far {
            max_so_far = a[i];
        }
        i += 1;
    }
    max_so_far
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn max_dafny_lsp(a: &[i32]) -> (x: usize)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x as int],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut x: usize = 0;
    let mut i: usize = 1;
    while i < a.len()
        invariant
            i <= a.len(),
            0 <= x < i,
            forall|k: int| 0 <= k < i ==> a[k] <= a[x as int],
    {
        if a[i] > a[x] {
            x = i;
        }
        i += 1;
    }
    x
}
// </vc-code>

fn main() {}
}