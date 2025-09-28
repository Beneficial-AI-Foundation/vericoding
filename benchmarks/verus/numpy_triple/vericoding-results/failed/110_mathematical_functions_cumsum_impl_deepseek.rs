// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn prefix_sum_mono_helper(a: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j <= a.len(),
    ensures
        prefix_sum(a, i) <= prefix_sum(a, j),
    decreases j - i
{
    if i < j {
        assert(0 <= j - 1 <= a.len());
        prefix_sum_mono_helper(a, i, j - 1);
        assert(prefix_sum(a, j) == prefix_sum(a, j - 1) + (a[j - 1] as int));
        assert(prefix_sum(a, j - 1) <= prefix_sum(a, j - 1) + (a[j - 1] as int));
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
{
    /* code modified by LLM (iteration 5): Add decreases clause to while loop */
    let len = a.len();
    if len == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::with_capacity(len);
    result.push(a[0]);
    
    let mut i = 1;
    while i < len
        invariant
            result.len() == i,
            i >= 1 && i <= len,
            forall|k: int| 0 <= k < i ==> result[k] as int == prefix_sum(a@, k),
        decreases len - i
    {
        proof {
            prefix_sum_mono_helper(a@, 0, i as int);
        }
        let prev = result[i - 1];
        let current_sum = prev + a[i];
        result.push(current_sum);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}