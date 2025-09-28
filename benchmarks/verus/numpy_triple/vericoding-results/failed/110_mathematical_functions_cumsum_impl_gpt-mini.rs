// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate prefix_sum at i to prefix_sum at i-1 */
fn lemma_prefix_sum_add(a: Seq<i32>, i: int)
    requires
        0 < i,
        i < a.len(),
    ensures
        prefix_sum(a, i) == prefix_sum(a, i - 1) + (a[i] as int),
{
    proof {
        // By definition of prefix_sum for i >= 1
        assert(prefix_sum(a, i) == prefix_sum(a, i - 1) + (a[i] as int));
    }
}

// </vc-helpers>

// <vc-spec>
spec fn prefix_sum(a: Seq<i32>, i: int) -> int
    decreases i
{
    if i < 0 || i >= a.len() {
        0
    } else if i == 0 {
        a[0] as int
    } else {
        prefix_sum(a, i - 1) + (a[i] as int)
    }
}

fn numpy_cumsum(a: Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == a.len(),
        a.len() > 0 ==> result[0] == a[0],
        forall|i: int| 0 < i < a.len() ==> result[i] == result[i - 1] + a[i],
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == prefix_sum(a@, i)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute cumulative sum using usize index and maintain invariant */
{
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= (i as int),
            (i as int) <= (a.len() as int),
            res.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> res[j as usize] as int == prefix_sum(a@, j),
        decreases
            a.len() - i
    {
        if i == 0 {
            if a.len() > 0 {
                res.push(a[0]);
            }
        } else {
            let prev = res[i - 1];
            let ai = a[i];
            let cum = prev + ai;
            proof {
                lemma_prefix_sum_add(a@, i as int);
                assert(res[i - 1] as int == prefix_sum(a@, (i as int) - 1));
                assert((res[i - 1] as int) + (ai as int) == prefix_sum(a@, i as int));
            }
            res.push(cum);
        }
        i = i + 1;
    }
    res
}

// </vc-code>


}
fn main() {}