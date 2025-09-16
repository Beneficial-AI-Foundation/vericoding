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
/* helper modified by LLM (iteration 5): cast i32 to int */
spec fn to_int(x: i32) -> int { x as int }
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
    /* code modified by LLM (iteration 5): use a tracked ghost sum to relate runtime accumulator and spec sum */
    let mut i: usize = 0;
    let mut acc: i128 = 0;
    let mut found: bool = false;
    let tracked mut s_sum: int = 0;
    while i < operations.len()
        invariant
            0 <= i as int <= operations@.len(),
            s_sum == sum(operations@.take(i as int).map(|_idx, j: i32| j as int)),
            acc as int == s_sum,
            found == (exists|k: int| 0 <= k <= i as int && sum(operations@.take(k).map(|_idx, j: i32| j as int)) < 0),
        decreases
            operations.len() - i
    {
        let elt: i32 = operations[i];
        acc = acc + (elt as i128);
        if acc < 0 {
            found = true;
        }
        proof {
            let elt_spec: i32 = operations@[i as int];
            // acc has been updated; use the loop invariant from before the update to relate acc and s_sum
            assert(acc as int == s_sum + (elt_spec as int));
            s_sum = s_sum + (elt_spec as int);
            assert(acc as int == s_sum);
            assert(s_sum == sum(operations@.take((i as int) + 1).map(|_idx, j: i32| j as int)));
            if acc < 0 {
                assert(s_sum < 0);
            }
        }
        i += 1;
    }
    found
}
// </vc-code>

}
fn main() {}