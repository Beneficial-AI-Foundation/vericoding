// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial lemma ensuring usize casts to non-negative int */
proof fn usize_nonneg(u: usize)
    ensures
        (u as int) >= 0,
{
    proof {
        assert(u as int >= 0);
    }
}

// </vc-helpers>

// <vc-spec>
fn square(arr: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] as int == arr[i] as int * arr[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use res@ and arr@ with int indices in invariants */
    let n: usize = arr.len();
    let mut res: Vec<i8> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            forall|j: int| 0 <= j < i as int ==> res@[j] as int == arr@[j] as int * arr@[j] as int,
        decreases n - i
    {
        let x: i8 = arr[i];
        let sq_i8: i8 = ((x as i32) * (x as i32)) as i8;
        res.push(sq_i8);
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}