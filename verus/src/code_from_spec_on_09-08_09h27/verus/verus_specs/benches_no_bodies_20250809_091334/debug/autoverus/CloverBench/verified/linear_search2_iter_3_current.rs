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
            /* code modified by LLM (iteration 1): added invariant to maintain existence guarantee */
            exists|j: int| (i <= j < a.len() as int) && a[j] == e,
        /* code modified by LLM (iteration 1): added decreases clause for termination */
        decreases a.len() - i
    {
        if a[i] == e {
            return i;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 1): replaced unreachable!() with proof that this point is unreachable */
    proof {
        assert(i == a.len());
        assert(forall|k: int| (0 <= k < i as int) ==> a[k] != e);
        assert(forall|k: int| (0 <= k < a.len() as int) ==> a[k] != e);
        assert(exists|j: int| (0 <= j < a.len() as int) && a[j] == e);
        assert(false);
    }
    0  // This line is unreachable but needed for compilation
}

} // verus!