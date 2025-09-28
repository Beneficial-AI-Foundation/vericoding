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
/* helper modified by LLM (iteration 5): used public arithmetic lemma for distributivity */
proof fn sum_range_bound_lemma(s: Seq<int>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
        forall|i: int| start <= i < end ==> -128 <= s[i] && s[i] <= 127,
    ensures
        (end - start) * -128 <= sum_range(s, start, end),
        sum_range(s, start, end) <= (end - start) * 127,
    decreases end - start
{
    if start < end {
        sum_range_bound_lemma(s, start + 1, end);
        vstd::arithmetic::mul_distributes_over_add(127, 1, end - start - 1);
        vstd::arithmetic::mul_distributes_over_add(-128, 1, end - start - 1);
    }
}

/* helper modified by LLM (iteration 5): used public arithmetic lemmas for division */
proof fn div_bounds_prove(sum: int, n: int, years_spec: Seq<int>)
    requires
        n > 0,
        years_spec.len() == n,
        sum == sum_range(years_spec, 0, n),
        forall|i: int| 0 <= i < years_spec.len() ==> -128 <= years_spec[i] && years_spec[i] <= 127,
    ensures
        -128 <= sum / n <= 127,
{
    sum_range_bound_lemma(years_spec, 0, n);
    vstd::arithmetic::div_is_monotonic(n * -128, sum, n);
    vstd::arithmetic::div_is_monotonic(sum, n * 127, n);
    vstd::arithmetic::mul_div_cancel(-128, n);
    vstd::arithmetic::mul_div_cancel(127, n);
}

fn sum_vec(v: &Vec<i8>) -> (total: i32)
    ensures
        total as int == sum_range(v@.map(|i, x| x as int), 0, v.len() as int),
{
    let mut s: i32 = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            s as int == sum_range(v@.map(|i, x| x as int), 0, i as int),
        decreases v.len() - i
    {
        s = s + v[i] as i32;
        i = i + 1;
    }
    s
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, years: Vec<i8>) -> (result: i8)
    requires n > 0 && years.len() == n as nat
    ensures result as int == sum_range(years@.map(|i, x| x as int), 0, years.len() as int) / (n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): logic relies on updated helpers */
    let total = sum_vec(&years);
    let avg = total / (n as i32);

    proof {
        let years_spec = years@.map(|i, x| x as int);
        assert forall|i: int| 0 <= i < years_spec.len() implies -128 <= years_spec[i] && years_spec[i] <= 127 by {};
        
        let sum_spec = sum_range(years_spec, 0, years.len() as int);
        
        div_bounds_prove(sum_spec, n as int, years_spec);
        
        assert(avg as int == sum_spec / (n as int));
        assert(-128 <= avg && avg <= 127);
    }

    let result = avg as i8;
    result
}
// </vc-code>


}

fn main() {}