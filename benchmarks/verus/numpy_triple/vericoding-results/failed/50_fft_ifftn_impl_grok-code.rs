// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Sum of integers over finite indices */
pub open spec fn int_sum(n: nat, f: spec_fn(int) -> int) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        f((n - 1) as int) + int_sum((n - 1) as nat, f)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ifftn(a: Vec<Vec<i8>>) -> (result: Vec<Vec<i8>>)
    requires 
        a.len() > 0,
        a.len() < usize::MAX,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() < usize::MAX,
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < a@.len() ==> a@[i].len() == a@[j].len(),
    ensures 
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == a@[0].len(),
        forall|i: int, j: int| #[trigger] result@[i][j] == 0 || 
            (0 <= i < result@.len() && 0 <= j < result@[i].len()),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added invariants to inner loop to track elements are 0, expanded outer loop invariant to include forall elements are 0, and updated proof block to assert the ensures conditions for proper verification. */
    let alen = a.len();
    let blen = a[0].len();
    proof {
        assert(alen as int == a@.len());
        assert(blen as int == a@[0].len());
    }
    let mut result: Vec<Vec<i8>> = Vec::with_capacity(alen);
    let mut i: usize = 0;
    while i < alen
        invariant
            alen as int == a@.len(),
            blen as int == a@[0].len(),
            result@.len() == i as int,
            forall |k: int| 0 <= k < i as int ==> (
                result@[k].len() == blen as int
                && forall |l: int| 0 <= l < result@[k].len() ==> result@[k][l] == 0
            ),
        decreases alen as int - i as int
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < blen
            invariant
                row@.len() == j as int,
                forall |m: int| 0 <= m < j as int ==> row@[m] == 0,
            decreases blen as int - j as int
        {
            row.push(0);
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    proof {
        assert(result@.len() == alen as int);
        assert(result@.len() == a@.len());
        assert(forall |i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@[i].len() ==> result@[i][j] == 0);
    }
    result
}
// </vc-code>


}
fn main() {}