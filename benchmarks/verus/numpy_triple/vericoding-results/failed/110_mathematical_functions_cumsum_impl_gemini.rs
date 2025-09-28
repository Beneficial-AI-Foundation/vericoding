// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): [retained correct lemma from previous attempt] */
proof fn lemma_prefix_sum_unfold(a: Seq<i32>, i: int)
    requires
        0 < i < a.len(),
    ensures
        prefix_sum(a, i) == prefix_sum(a, i - 1) + (a[i] as int),
{
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
{
    /* code modified by LLM (iteration 3): [wrapped lemma call in a proof block to fix compilation error] */
    let n = a.len();
    if n == 0 {
        return Vec::new();
    }

    let mut result = Vec::<i32>::with_capacity(n);
    result.push(a[0]);

    let mut i: usize = 1;
    while i < n
        invariant
            n == a.len(),
            1 <= i && i <= n,
            result.len() == i,
            a.len() > 0 ==> result@[0] == a@[0],
            forall|j: int| 0 < j < i as int ==> result@[j] == result@[j - 1] + a@[j],
            forall|j: int| 0 <= j < i as int ==> result@[j] as int == prefix_sum(a@, j),
        decreases n - i
    {
        proof {
            lemma_prefix_sum_unfold(a@, i as int);
        }
        let new_val = result[i - 1] + a[i];
        result.push(new_val);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}