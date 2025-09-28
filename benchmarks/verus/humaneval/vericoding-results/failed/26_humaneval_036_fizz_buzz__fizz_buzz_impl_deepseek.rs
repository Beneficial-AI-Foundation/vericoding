// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count7_r(x: nat) -> nat
    decreases x
{
    let lst = if x % 10 == 7 { 1 } else { 0 };
    if x < 10 { lst } else { lst + count7_r(x / 10) }
}

spec fn sum(s: Seq<nat>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum(s.subrange(1, s.len() as int)) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add proper spec function for sequence sum verification */
spec fn seq_sum_helper(s: Seq<nat>, start: int, end: int) -> nat
    decreases end - start
{
    if start >= end {
        0
    } else {
        s[start] + seq_sum_helper(s, start + 1, end)
    }
}

proof fn sum_equals_seq_sum_helper(s: Seq<nat>, start: int, end: int)
    requires 0 <= start <= end <= s.len()
    ensures sum(s.subrange(start, end)) == seq_sum_helper(s, start, end)
    decreases end - start
{
    reveal(sum);
    if start < end {
        sum_equals_seq_sum_helper(s, start + 1, end);
    }
}

proof fn count7_for_zero()
    ensures count7_r(0) == 0
{
    reveal(count7_r);
}

proof fn count7_div_10(x: nat)
    requires x >= 10
    ensures count7_r(x) == count7_r(x / 10) + (if x % 10 == 7 { 1nat } else { 0nat })
{
    reveal(count7_r);
}

fn count7_iter(x: u8) -> (cnt: u8)
    ensures cnt as nat == count7_r(x as nat)
    decreases x as int
{
    if x < 10 {
        if x == 7 { 1 } else { 0 }
    } else {
        let digit = x % 10;
        let sub_x = x / 10;
        let sub_cnt = count7_iter(sub_x);
        if digit == 7 {
            sub_cnt + 1
        } else {
            sub_cnt
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn fizz_buzz(n: u8) -> (result: u8)
    ensures result as nat == sum(
        Seq::new(n as nat, |i: int| 
            if 0 <= i < n as nat && (i % 11 == 0 || i % 13 == 0) { count7_r(i as nat) } else { 0 }
        )
    )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix compilation error by removing unnecessary ensures */
    let mut total: u8 = 0;
    let mut i: u8 = 0;
    
    while i < n
        invariant
            total as nat == sum(
                Seq::new(i as nat, |j: int| 
                    if 0 <= j < i as nat && (j % 11 == 0 || j % 13 == 0) { count7_r(j as nat) } else { 0nat }
                )
            ),
            i <= n,
    {
        if i % 11 == 0 || i % 13 == 0 {
            let cnt = count7_iter(i);
            total = total + cnt;
        }
        i = i + 1;
    }
    
    total
}
// </vc-code>


}

fn main() {}