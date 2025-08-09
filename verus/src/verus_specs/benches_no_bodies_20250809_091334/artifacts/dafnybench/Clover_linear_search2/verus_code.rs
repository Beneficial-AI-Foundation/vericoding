use vstd::prelude::*;

verus! {
    fn linear_search(a: &[int], e: int) -> (n: usize)
        requires 
            exists|i: int| 0 <= i < a.len() && a[i] == e,
        ensures 
            0 <= n < a.len(),
            a[n as int] == e,
            forall|k: int| 0 <= k < n ==> a[k] != e,
    {
    return 0;  // TODO: Remove this line and implement the function body
    }
}

fn main() {}