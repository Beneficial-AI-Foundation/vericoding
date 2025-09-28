// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, heights: Seq<int>) -> bool {
    n > 0 && heights.len() == n &&
    (forall|i: int| 0 <= i < n ==> #[trigger] heights[i] >= 0) &&
    (forall|i: int| 0 <= i < n-1 ==> #[trigger] heights[i] < heights[i+1])
}

spec fn valid_output(n: int, result: Seq<int>) -> bool {
    result.len() == n &&
    (forall|i: int| 0 <= i < n ==> #[trigger] result[i] >= 0) &&
    (forall|i: int| 0 <= i < n-1 ==> #[trigger] result[i] <= result[i+1]) &&
    (forall|i: int| 0 <= i < n-1 ==> #[trigger] result[i+1] - result[i] <= 1)
}

spec fn is_stable(result: Seq<int>) -> bool {
    forall|i: int| 0 <= i < result.len()-1 ==> !(#[trigger] result[i] + 2 <= result[i+1])
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.subrange(1, s.len() as int)) }
}
// </vc-preamble>

// <vc-helpers>

proof fn distribute_sum(s: Seq<int>)
    ensures
        sum_seq(s) == s.fold_by(0, |acc: int, x: int| acc + x),
    decreases s.len()
{
    if s.len() == 0 {
        assert(sum_seq(s) == 0);
        assert(s.fold_by(0, |acc: int, x: int| acc + x) == 0);
    } else {
        let head = s[0];
        let tail = s.subrange(1, s.len() as int);
        assert(sum_seq(s) == head + sum_seq(tail));
        assert(s.fold_by(0, |acc: int, x: int| acc + x) == head + tail.fold_by(0, |acc: int, x: int| acc + x));
        distribute_sum(tail);
    }
}

proof fn sum_constant_increment_proof(heights: Seq<int>, result: Seq<int>)
    requires
        heights.len() == result.len(),
        result.len() > 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() - 1 ==> result[i + 1] - result[i] <= 1,
        sum_seq(result) == sum_seq(heights),
    ensures
        is_stable(result),
{
    assert forall|i: int| 0 <= i < result.len() - 1 implies !(result[i] + 2 <= result[i + 1]) by {
        if result[i] + 2 <= result[i + 1] {
            assert(result[i + 1] - result[i] > 1);
            assert(false);
        }
    };
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, heights: Vec<i8>) -> (result: Vec<i8>)
    requires 
        valid_input(n as int, heights@.map(|i, v| v as int))
    ensures 
        valid_output(n as int, result@.map(|i, v| v as int)) &&
        sum_seq(result@.map(|i, v| v as int)) == sum_seq(heights@.map(|i, v| v as int)) &&
        is_stable(result@.map(|i, v| v as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed Seq methods, type conversions, and arithmetic operations */
    let mut result_vec = Vec::new();
    
    proof {
        let ghost_n: int = n as int;
        let ghost_heights = heights@.map(|i: int, v: i8| v as int);
        let total_sum = sum_seq(ghost_heights);
        let base_height = total_sum / ghost_n;
        let mut remainder = total_sum % ghost_n;
        
        let mut current: int = 0;
        
        while current < ghost_n
            invariant
                result_vec@.len() as int == current,
                sum_seq(result_vec@.map(|i: int, v: i8| v as int)) + base_height * (ghost_n - current) + remainder == total_sum,
                0 <= remainder <= ghost_n - current,
                current <= ghost_n
        {
            let next_height = if remainder > 0 {
                remainder = remainder - 1;
                base_height + 1
            } else {
                base_height
            };
            
            result_vec.push(next_height as i8);
            current = current + 1;
        }
    }
    
    result_vec
}
// </vc-code>


}

fn main() {}