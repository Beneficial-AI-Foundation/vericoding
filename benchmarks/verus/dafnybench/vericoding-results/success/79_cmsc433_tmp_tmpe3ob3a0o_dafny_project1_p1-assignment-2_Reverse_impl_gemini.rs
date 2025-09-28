// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn reverse(a: &Vec<i32>) -> (a_rev: Vec<i32>)
    ensures
        a_rev.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] == a_rev[a_rev.len() - i - 1]
// </vc-spec>
// <vc-code>
{
    let mut a_rev: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a_rev@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> a_rev@[k] == a@[a@.len() - 1 - k],
        decreases a.len() - i
    {
        a_rev.push(a[a.len() - 1 - i]);
        i = i + 1;
    }
    a_rev
}
// </vc-code>

}
fn main() {}