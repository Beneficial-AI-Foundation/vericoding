// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_range(s: Seq<int>, start: int, end: int) -> int
    decreases end - start when 0 <= start <= end <= s.len()
{
    if start == end {
        0
    } else {
        s[start] + sum_range(s, start + 1, end)
    }
}

spec fn valid_input(n: int, years: Seq<int>) -> bool
{
    n > 0 && years.len() == n
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_seq_map_sum_preservation(s: Vec<i8>) -> (total: int)
    ensures total == sum_range(s@.map(|j, x| x as int), 0, s.len() as int)
{
    let mut sum = 0;
    let mut i: int = 0;
    let len: int = s.len() as int;
    while i < len
        invariant
            0 <= i <= len,
            sum == sum_range(s@.map(|j, x| x as int), 0, i),
        decreases len - i
    {
        sum = sum + s[i as usize] as int;
        i = i + 1;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, years: Vec<i8>) -> (result: i8)
    requires n > 0 && years.len() == n as nat
    ensures result as int == sum_range(years@.map(|i, x| x as int), 0, years.len() as int) / (n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed ghost code usage and added proper variable declarations */
    let n_int: int = n as int;
    let len_int: int = years.len() as int;
    
    let ghost_sum: int;
    proof {
        let total = lemma_seq_map_sum_preservation(years.clone());
        assert(total == sum_range(years@.map(|j, x| x as int), 0, len_int));
        ghost_sum = total;
    }
    
    let result = (ghost_sum / n_int) as i8;
    result
}
// </vc-code>


}

fn main() {}