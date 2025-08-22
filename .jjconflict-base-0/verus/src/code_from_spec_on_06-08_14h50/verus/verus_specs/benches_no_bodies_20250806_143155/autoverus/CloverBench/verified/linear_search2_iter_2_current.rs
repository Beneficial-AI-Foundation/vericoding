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
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| (0 <= k < i as int) ==> a[k] != e,
            exists|j: int| (0 <= j < a.len() as int) && a[j] == e,
    {
        if a[i] == e {
            return i;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 1): replaced unreachable!() with proof that this case is impossible */
    proof {
        // We know that exists j such that a[j] == e
        // We also know that for all k < i, a[k] != e
        // Since i == a.len(), we've checked all elements
        // This contradicts the existence requirement
        assert(i == a.len());
        assert(forall|k: int| (0 <= k < i as int) ==> a[k] != e);
        assert(exists|j: int| (0 <= j < a.len() as int) && a[j] == e);
        assert(false); // contradiction
    }
    0 // This line is never reached due to the proof above
}

} // verus!