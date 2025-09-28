// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn linear_search(a: &[i32], e: i32) -> (n: usize)
    ensures 
        n <= a.len(),
        n == a.len() || a[n as int] == e,
        forall|i: int| 0 <= i < n ==> e != a[i],
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != e,
        decreases a.len() - i
    {
        if a[i] == e {
            return i;
        }
        i = i + 1;
    }
    a.len()
}
// </vc-code>

}
fn main() {}