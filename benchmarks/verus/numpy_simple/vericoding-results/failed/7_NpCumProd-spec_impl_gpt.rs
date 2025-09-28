// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed arithmetic proof syntax and simplified */
proof fn lemma_prev_index(i: int, n: int)
    requires
        0 < i,
        i <= n,
    ensures
        0 <= i - 1,
        i - 1 < n,
{
    assert(0 <= i - 1);
    assert(i - 1 < n);
}

// </vc-helpers>

// <vc-spec>
fn cum_prod(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        result[0] == a[0],
        forall|i: int| 0 < i < a.len() ==> result[i] as int == result[i-1] as int * a[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): iterative cumulative product with loop invariants */
    let n = a.len();
    let mut result: Vec<i8> = Vec::new();
    result.push(a[0]);

    let mut i: usize = 1;
    while i < n
        invariant
            n == a.len(),
            1 <= i <= n,
            result.len() == i,
            result.len() <= n,
            result.len() > 0,
            result[0] == a[0],
            forall|j: int| 0 < j < i as int ==> result[j] as int == result[j - 1] as int * a[j] as int,
        decreases n - i
    {
        let j = i - 1;
        let prev = result[j];
        let ai = a[i];
        let prod_i16: i16 = (prev as i16) * (ai as i16);
        let prod: i8 = prod_i16 as i8;
        result.push(prod);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}