use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue is a syntax error in the code section
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn linear_search(a: &[i32], e: i32) -> (n: usize)
    ensures 
        n <= a.len(),
        n == a.len() || a[n as int] == e,
        forall|i: int| 0 <= i < n ==> e != a[i],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn linear_search(a: &[i32], e: i32) -> (n: usize)
    ensures
        n <= a.len(),
        n == a.len() || a[n as int] == e,
        forall|i: int| 0 <= i < n ==> e != a[i],
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < i ==> e != a[k],
    {
        if a[i] == e {
            return i;
        }
        i = i + 1;
    }
    i
}
// </vc-code>

fn main() {}

}