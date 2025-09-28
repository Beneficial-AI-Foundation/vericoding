// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max_prefix(s: Seq<int>, i: nat) -> int
    recommends i < s.len()
    decreases i
{
    if i == 0 { s[0] }
    else if s[i as int] > max_prefix(s, (i-1) as nat) { s[i as int] }
    else { max_prefix(s, (i-1) as nat) }
}

spec fn max_seq(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
    when s.len() > 0
{
    if s.len() == 1 { s[0] }
    else {
        let sub_seq = s.subrange(0, (s.len()-1) as int);
        if s[(s.len()-1) as int] > max_seq(sub_seq) { s[(s.len()-1) as int] }
        else { max_seq(sub_seq) }
    }
}

spec fn max_expression(n: int, p: int, q: int, r: int, a: Seq<int>) -> int
    recommends n > 0 && a.len() == n
{
    let s1 = Seq::new(n as nat, |i: int| a[i] * p);
    let s2 = Seq::new(n as nat, |i: int| max_prefix(s1, i as nat) + a[i] * q);
    let s3 = Seq::new(n as nat, |i: int| max_prefix(s2, i as nat) + a[i] * r);
    max_seq(s3)
}

spec fn valid_input(n: int, a: Seq<int>) -> bool
{
    n > 0 && a.len() == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Retained helper functions for max operation. */
spec fn spec_max(a: int, b: int) -> int {
    if a > b { a } else { b }
}

fn max(a: i64, b: i64) -> (c: i64)
    ensures
        c as int == spec_max(a as int, b as int),
{
    if a > b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, p: i8, q: i8, r: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map(|i, x| x as int))
    ensures result as int == max_expression(n as int, p as int, q as int, r as int, a@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed compilation errors by using 'ghost let' for spec variables. */
    ghost let n_int = n as int;
    ghost let p_int = p as int;
    ghost let q_int = q as int;
    ghost let r_int = r as int;
    ghost let a_seq = a@.map(|_idx, val: i8| val as int);

    ghost let s1 = Seq::new(n_int as nat, |j: int| a_seq[j] * p_int);
    ghost let s2 = Seq::new(n_int as nat, |j: int| max_prefix(s1, j as nat) + a_seq[j] * q_int);
    ghost let s3 = Seq::new(n_int as nat, |j: int| max_prefix(s2, j as nat) + a_seq[j] * r_int);

    let p_i64 = p as i64;
    let q_i64 = q as i64;
    let r_i64 = r as i64;

    let a0_i64 = a[0] as i64;
    let mut max1 = p_i64 * a0_i64;
    let mut max2 = max1 + q_i64 * a0_i64;
    let mut ans = max2 + r_i64 * a0_i64;

    let mut i: i8 = 1;
    while i < n
        invariant
            1 <= i <= n,
            max1 as int == max_prefix(s1, (i - 1) as nat),
            max2 as int == max_prefix(s2, (i - 1) as nat),
            ans as int == max_seq(s3.subrange(0, i as int)),
        decreases n - i
    {
        let ai_i64 = a[i as usize] as i64;
        
        max1 = max(max1, p_i64 * ai_i64);
        max2 = max(max2, max1 + q_i64 * ai_i64);
        ans = max(ans, max2 + r_i64 * ai_i64);
        
        i = i + 1;
    }

    ans as i8
}
// </vc-code>


}

fn main() {}