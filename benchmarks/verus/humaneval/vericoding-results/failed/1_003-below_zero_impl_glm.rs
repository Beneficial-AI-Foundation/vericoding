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
    let mut current_sum = 0;
    let mut i = 0;
    while i < operations@.len()
        invariant
            0 <= i <= operations@.len(),
            current_sum == sum(operations@.take(i).map(|_idx, j: i32| j as int)),
            forall |j: int| 0 <= j < i ==> 
                sum(operations@.take(j).map(|_idx, j: i32| j as int)) >= 0,
        decreases operations@.len() - i
    {
        let next_op = operations[i];
        current_sum = current_sum + (next_op as int);
        if current_sum < 0 {
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-code>

}
fn main() {}