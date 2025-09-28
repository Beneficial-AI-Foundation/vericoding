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
/* helper modified by LLM (iteration 5): convert Vec<i8> to Seq<int> */
spec fn vec_i8_to_seq(v: Vec<i8>) -> Seq<int> {
    v@.map(|i, x| x as int)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, years: Vec<i8>) -> (result: i8)
    requires n > 0 && years.len() == n as nat
    ensures result as int == sum_range(years@.map(|i, x| x as int), 0, years.len() as int) / (n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute average using helper conversion and loop invariant */
{
    let tracked years_seq: Seq<int> = vec_i8_to_seq(years);
    let mut i: usize = 0;
    let mut sum_rt: i32 = 0;
    while i < years.len()
        invariant
            i <= years.len(),
            (sum_rt as int) == sum_range(years_seq, 0, i as int),
        decreases years.len() - i
    {
        let v: i8 = years[i];
        sum_rt = sum_rt + (v as i32);
        i = i + 1;
    }
    let avg32: i32 = sum_rt / (n as i32);
    proof {
        assert((sum_rt as int) == sum_range(years_seq, 0, years.len() as int));
        assert((avg32 as int) == sum_range(years_seq, 0, years.len() as int) / (n as int));
    }
    (avg32 as i8)
}
// </vc-code>


}

fn main() {}