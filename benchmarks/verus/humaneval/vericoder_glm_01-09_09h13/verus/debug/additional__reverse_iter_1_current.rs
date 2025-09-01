use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn reverse(a: &[i32]) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut result = vec![0; n];
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == n,
            forall|k: int| 0 <= k < (i as int) ==> result[k as usize] == a[n - 1 - (k as usize)],
    {
        let j = n - 1 - i;
        result.set(i,
// </vc-code>

fn main() {}
}