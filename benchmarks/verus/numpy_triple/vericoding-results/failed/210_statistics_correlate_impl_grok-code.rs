// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Removed invalid requires clause from spec function */
spec fn partial_sum(a: Seq<i32>, v: Seq<i32>, i: int, j: int) -> int
    decreases v.len() - j
{
    if j == v.len() {
        0
    } else {
        a[i + j] * v[j] + partial_sum(a, v, i, j + 1)
    }
}

/* helper modified by LLM (iteration 4): Adjusted for removed requires in spec fn */
proof fn lemma_partial_sum_equals_correlation_sum(a: Seq<i32>, v: Seq<i32>, i: int)
    ensures partial_sum(a, v, i, 0) == correlation_sum(a, v, i)
    decreases v.len()
{
    if v.len() == 0 {
        assert(partial_sum(a, Seq::<i32>::empty(), i, 0) == 0);
        assert(correlation_sum(a, Seq::<i32>::empty(), i) == 0);
    } else {
        assert(partial_sum(a, v, i, 0) == a[i + 0] * v[0] + partial_sum(a, v, i, 1));
        assert(correlation_sum(a, v, i) == a[i] * v[0] + correlation_sum(a, v.skip(1), i + 1));
        lemma_partial_sum_equals_correlation_sum(a, v.skip(1), i + 1);
    }
}

// </vc-helpers>

// <vc-spec>
spec fn correlation_sum(a: Seq<i32>, v: Seq<i32>, k: int) -> int
    decreases v.len()
{
    if v.len() == 0 {
        0
    } else {
        a[k] * v[0] + correlation_sum(a, v.skip(1), k + 1)
    }
}

fn correlate(a: Vec<i32>, v: Vec<i32>) -> (result: Vec<i32>)
    requires 
        v.len() > 0,
        v.len() <= a.len(),
    ensures
        result.len() == a.len() + 1 - v.len(),
        forall|k: int| 0 <= k < result.len() ==> 
            result[k] == correlation_sum(a@, v@, k),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Adjusted invariants for removed requires in spec fn */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    let max_i = a.len() + 1 - v.len();
    while i < max_i
        invariant
            i <= max_i,
            result.len() == i,
            forall|idx: int| 0 <= idx < i ==> 
                result@[idx] == correlation_sum(a@, v@, idx),
        decreases max_i - i
    {
        let mut sum: i32 = 0;
        let mut j: usize = v.len();
        while j > 0
            invariant
                j <= v.len(),
                sum == partial_sum(a@, v@, i as int, j as int),
            decreases j
        {
            j -= 1;
            sum += a[i + j] * v[j];
        }
        proof {
            lemma_partial_sum_equals_correlation_sum(a@, v@, i as int);
            assert(sum == correlation_sum(a@, v@, i as int));
        }
        result.push(sum);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}