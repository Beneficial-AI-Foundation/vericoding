use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn linear_search(a: &[i32], e: i32) -> (n: usize)
    requires exists|i: int| 0 <= i < a.len() && a[i] == e,
    ensures ({
        &&& 0 <= n < a.len() 
        &&& a[n as int] == e
        &&& forall|k: int| 0 <= k < n as int ==> a[k] != e
    }),
{
// </vc-spec>
// </vc-spec>

// <vc-code>
let mut i: usize = 0;
while i < a.len()
    invariant
        0 <= i <= a.len(),
        forall|k: int| 0 <= k < i as int ==> a[k] != e,
        exists|k: int| i as int <= k < a.len() && a[k] == e
{
    if a[i] == e {
        return i;
    }
    i = i + 1;
}
unreachable!();
// </vc-code>

fn main() {}

}