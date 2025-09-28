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
    /* code modified by LLM (iteration 2): replaced map with loop to avoid pattern issue */
    let mut total: i32 = 0;
    for i in 0..heights.len() {
        total += heights[i] as i32;
    }
    let n_int = n as i32;
    let a_min = total / n_int;
    let remainder = total % n_int;
    let mut result = Vec::with_capacity(n as usize);
    for i in 0..n_int {
        if i < n_int - remainder {
            result.push(a_min as i8);
        } else {
            result.push((a_min + 1) as i8);
        }
    }
    result
}
// </vc-code>


}

fn main() {}