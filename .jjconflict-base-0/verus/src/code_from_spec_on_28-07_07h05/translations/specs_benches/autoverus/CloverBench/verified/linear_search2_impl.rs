use vstd::prelude::*;

fn main() {}

verus! {

pub fn linear_search(a: &Vec<i32>, e: i32) -> (n: usize)
    requires
        exists|i: int| (0 <= i < a.len() as int) && a[i] == e,
    ensures
        0 <= n < a.len(),
        a[n as int] == e,
        forall|k: int| (0 <= k < n as int) ==> a[k] != e,
{
    let mut i = 0;
    /* code modified by LLM (iteration 1): Added decreases clause to prove loop termination */
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| (0 <= k < i as int) ==> a[k] != e,
            exists|j: int| (i as int <= j < a.len() as int) && a[j] == e,
        decreases a.len() - i,
    {
        if a[i] == e {
            return i;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 1): Added assertion to prove unreachability and replaced unreachable!() with proper return */
    assert(false); // This should never be reached due to loop invariant
    0 // This line will never execute, but satisfies the compiler
}

} // verus!