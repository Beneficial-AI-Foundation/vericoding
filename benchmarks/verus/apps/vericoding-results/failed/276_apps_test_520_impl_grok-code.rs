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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, years: Vec<i8>) -> (result: i8)
    requires n > 0 && years.len() == n as nat
    ensures result as int == sum_range(years@.map(|i, x| x as int), 0, years.len() as int) / (n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed compilation error by changing wildcard _ to variable idx in closure pattern */
{
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < years.len()
        invariant
            0 <= i <= years.len(),
            sum as int == sum_range(years@.map(|idx, x| x as int), 0, i as int),
        decreases years.len() - i
    {
        let val = years[i] as i64;
        sum = sum + val;
        i = i + 1;
    }
    let n_int = n as i64;
    let result = sum / n_int;
    (result as i8)
}
// </vc-code>


}

fn main() {}