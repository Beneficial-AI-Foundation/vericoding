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
{
/* code modified by LLM (iteration 5): fixing type mismatches by using nat for len and i, indexing with cast to int to avoid usize cast */
    let len = operations@.len();
    let tracked mut sum_tracked: int = 0;
    let mut sum_exec: i32 = 0;
    let mut i: nat = 0;
    while i < len
        invariant
            i <= len,
            sum_tracked == sum_exec as int,
            sum_tracked == sum(operations@.take(i as int).map(|_idx, j: i32| j as int)),
        decreases len - i
    {
        let val = operations@[(i as int)];
        proof {
            sum_tracked = sum_tracked + (val as int);
        }
        match sum_exec.checked_add(val) {
            Some(new_sum) => {
                sum_exec = new_sum;
                if sum_exec < 0 {
                    return true;
                }
            }
            None => { } //overflow impossible per requires
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}