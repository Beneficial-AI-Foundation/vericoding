// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.subrange(1, s.len() as int)) }
}

spec fn min_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 
        0
    } else if s.len() == 1 { 
        s[0] 
    } else { 
        let rest_min = min_seq(s.subrange(1, s.len() as int));
        if s[0] <= rest_min { s[0] } else { rest_min }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): absolute value for i8 as int */
spec fn abs_i8(x: i8) -> int
{
    if x < 0 { -x as int } else { x as int }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<i8>) -> (result: i8)
    requires a@.len() >= 2
    ensures ({
        let count_neg = Set::new(|i: int| 0 <= i < a@.len() && a@[i] < 0).len();
        let sum_abs = sum_seq(Seq::new(a@.len(), |i: int| if a@[i] < 0 { -a@[i] as int } else { a@[i] as int }));
        let min_abs = min_seq(Seq::new(a@.len(), |i: int| if a@[i] < 0 { -a@[i] as int } else { a@[i] as int }));
        result as int == if count_neg % 2 == 0 { sum_abs } else { sum_abs - 2 * min_abs }
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement solve without ghost blocks, track sum, min, count using concrete vars and invariants */
    let n = a.len();
    let mut i: usize = 0;
    let mut sum_abs_i32: i32 = 0;
    let mut min_abs_i32: i32 = 0;
    let mut count_neg_usize: usize = 0;
    while i < n
        invariant
            0 <= i as int && i as int <= n as int,
            sum_abs_i32 as int == sum_seq(Seq::new(i as int, |k: int| abs_i8(a@[k]))),
            min_abs_i32 as int == min_seq(Seq::new(i as int, |k: int| abs_i8(a@[k]))),
            count_neg_usize as int == Set::new(|k: int| 0 <= k && k < i as int && a@[k] < 0).len() as int,
        decreases n as int - i as int
    {
        let cur: i8 = a[i];
        let cur_abs_i32: i32 = if cur < 0 { -(cur as i32) } else { cur as i32 };
        if cur < 0 {
            count_neg_usize = count_neg_usize + 1;
        }
        sum_abs_i32 = sum_abs_i32 + cur_abs_i32;
        if i == 0 {
            min_abs_i32 = cur_abs_i32;
        } else {
            if cur_abs_i32 < min_abs_i32 {
                min_abs_i32 = cur_abs_i32;
            }
        }
        i = i + 1;
    }
    let result_i32: i32 = if (count_neg_usize % 2) == 0 {
        sum_abs_i32
    } else {
        sum_abs_i32 - 2 * min_abs_i32
    };
    result_i32 as i8
}
// </vc-code>


}

fn main() {}