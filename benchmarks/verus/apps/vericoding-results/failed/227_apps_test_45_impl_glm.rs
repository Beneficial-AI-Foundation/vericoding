// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool
{
    n > 0 && k > 0
}

spec fn is_strictly_increasing(s: Seq<int>) -> bool
{
    forall|i: int| 0 <= i < s.len() - 1 ==> #[trigger] s[i] < s[i+1]
}

spec fn all_positive(s: Seq<int>) -> bool
{
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] > 0
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.subrange(1, s.len() as int)) }
}

spec fn valid_sequence(s: Seq<int>, n: int, k: int) -> bool
{
    s.len() == k && all_positive(s) && is_strictly_increasing(s) && sum_seq(s) == n
}

spec fn is_possible(n: int, k: int) -> bool
{
    k * (k + 1) / 2 <= n
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: Vec<i8>)
    requires 
        valid_input(n as int, k as int)
    ensures 
        ((result.len() == 1 && result[0] == -1) || 
         (valid_sequence(result@.map(|_i: int, x: i8| x as int), n as int, k as int))) &&
        ((result.len() == 1 && result[0] == -1) <==> !is_possible(n as int, k as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed for loop to use Range instead of RangeInclusive */
{
    let n_val = n as i32;
    let k_val = k as i32;
    if k_val > 15 {
        return vec![-1];
    }
    let base_sum = k_val * (k_val + 1) / 2;
    if base_sum > n_val {
        return vec![-1];
    }
    let extra = n_val - base_sum;
    let mut seq = Vec::with_capacity(k_val as usize);
    for i in 1..k_val+1 {
        seq.push(i as i8);
    }
    let mut extra_remaining = extra;
    let mut index = k_val - 1;
    while extra_remaining > 0 && index >= 0 {
        let max_add = k_val - 1 - index;
        let add = if extra_remaining < max_add {
            extra_remaining
        } else {
            max_add
        };
        seq[index as usize] += add as i8;
        extra_remaining -= add;
        index -= 1;
    }
    assert(extra_remaining == 0);
    seq
}
// </vc-code>


}

fn main() {}