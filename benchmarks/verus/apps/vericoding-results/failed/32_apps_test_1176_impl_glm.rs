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
/* helper modified by LLM (iteration 5): added helper function to compute absolute value */
spec fn abs_val(x: i8) -> int
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
    /* code modified by LLM (iteration 5): replaced int with i8 for non-ghost variables */
    let mut count_neg: i8 = 0;
    let mut sum_abs: i8 = 0;
    let first = a[0];
    let mut min_abs: i8 = if first < 0 { -first } else { first };
    if first < 0 {
        count_neg += 1;
    }
    sum_abs = min_abs;

    for i in 1..a.len() {
        let x = a[i];
        let abs_x: i8 = if x < 0 { -x } else { x };
        if x < 0 {
            count_neg += 1;
        }
        sum_abs += abs_x;
        if abs_x < min_abs {
            min_abs = abs_x;
        }
    }

    let result_int: i8 = if count_neg % 2 == 0 {
        sum_abs
    } else {
        sum_abs - 2 * min_abs
    };

    result_int
}
// </vc-code>


}

fn main() {}