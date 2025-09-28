// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Kept lemma for inductive step in prefix_sum proof. */
proof fn lemma_prefix_sum_inductive_step(a: Seq<i32>, i: int)
    requires
        0 <= i < a.len() - 1,
    ensures
        prefix_sum(a, i + 1) == prefix_sum(a, i) + (a[i + 1] as int),
by (compute)

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
/* code modified by LLM (iteration 5): Implemented using current sum variable to maintain prefix_sum invariant and prove postconditions. */
{
    let mut result = Vec::new();
    let mut current: i32 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> result@[j] as int == prefix_sum(a@, j),
            current as int == prefix_sum(a@, i as int),
        decreases a.len() - i
    {
        current = current + a[i];
        result.push(current);
        i = i + 1;
    }
    proof {
        forall|i| 1 <= i < a.len() {
            lemma_prefix_sum_inductive_step(a@, i - 1);
        }
    }
    result
}

// </vc-code>


}
fn main() {}