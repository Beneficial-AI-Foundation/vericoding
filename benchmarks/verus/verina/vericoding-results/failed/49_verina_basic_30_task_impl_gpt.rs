// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): range lemma for usize -> int, used to apply non-zero divisor precondition */
proof fn lemma_usize_in_range(i: usize, len: usize)
    requires
        i < len,
    ensures
        0 <= (i as int) < (len as int),
{
    assert(0 <= (i as int));
    assert((i as int) < (len as int));
}
// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement loop over indices, maintain invariants, and use helper to show divisors are non-zero */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            res.len() == i,
            0 <= (i as int) <= (a.len() as int),
            i <= a.len(),
            i <= b.len(),
            forall|j: int| 0 <= j < (i as int) ==> res[j] == a[j] % b[j],
        decreases (a.len() as int) - (i as int)
    {
        proof { assert(a.len() == b.len()); }
        proof { lemma_usize_in_range(i, b.len()); }
        proof { assert(b[(i as int)] != 0); }

        let ai = a[i];
        let bi = b[i];
        res.push(ai % bi);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}