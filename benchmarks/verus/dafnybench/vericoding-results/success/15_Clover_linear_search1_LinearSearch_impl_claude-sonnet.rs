use vstd::prelude::*;

verus! {

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
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> e != a[j],
        decreases a.len() - i,
    {
        if a[i] == e {
            return i;
        }
        i += 1;
    }
    i
}
// </vc-code>

fn main() {}

}