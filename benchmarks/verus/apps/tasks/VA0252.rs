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
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}