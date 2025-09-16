// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum(s.skip(1))
    }
}

spec fn sum_other_way(s: Seq<int>) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[s.len() - 1] + sum_other_way(s.take(s.len() - 1))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixing compilation error by removing incorrect @[proof] usage */
fn partial_sum_below_zero(ops: &Vec<i32>) -> bool {
    let mut total: i32 = 0;
    for i in 0..ops.len()
        invariant
            total as int == sum(ops@.take(i).map(|_idx, k: i32| k as int)),
    {
        total = total + ops[i];
        if total < 0 {
            return true;
        }
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i32>) -> (result: bool)

    requires
        forall|i: int|
            0 <= i <= operations@.len() ==> sum(operations@.take(i).map(|_idx, j: i32| j as int))
                <= i32::MAX,

    ensures
        result <==> exists|i: int|
            0 <= i <= operations@.len() && sum(operations@.take(i).map(|_idx, j: i32| j as int))
                < 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): call helper function with i32-based partial sum */
{
    partial_sum_below_zero(&operations)
}
// </vc-code>

}
fn main() {}