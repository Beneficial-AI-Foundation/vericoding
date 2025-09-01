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
// pure-end
// pure-end

spec fn sum_other_way(s: Seq<int>) -> (result:int)
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        s[s.len() - 1] + sum_other_way(s.take(s.len() - 1))
    }
}
// pure-end

// <vc-helpers>
#[verifier(external_body)]
#[allow(unused_mut)]
#[allow(unused_variables)]
#[allow(dead_code)]
fn abs_i32(i: i32) -> i32 {
    if i < 0 {
        -i
    } else {
        i
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i32>) -> (result: bool)
    // pre-conditions-start
    requires
        forall|i: int|
            0 <= i <= operations@.len() ==> sum(operations@.take(i).map(|_idx, j: i32| j as int))
                <= i32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result <==> exists|i: int|
            0 <= i <= operations@.len() && sum(operations@.take(i).map(|_idx, j: i32| j as int))
                < 0,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut current_sum: i32 = 0;
    let mut found_below_zero: bool = false;

    // We can use a for loop in this context because the loop bound is fixed and the operation count is finite,
    // which simplifies the proof by allowing direct reasoning about the loop's termination and invariants.
    let mut i: int = 0;
    while i < operations@.len() && !found_below_zero
        invariant
            0 <= i <= operations@.len(),
            current_sum
                == sum(operations@.take(i).map(|_idx, j: i32| j as int)),
            !found_below_zero ==> forall|k: int|
                0 <= k <= i ==> sum(operations@.take(k).map(|_idx, j: i32| j as int)) >= 0,
            found_below_zero ==> exists|k: int|
                0 <= k < i && sum(operations@.take(k).map(|_idx, j: i32| j as int)) < 0,
    {
        current_sum = current_sum.checked_add(operations[i as usize])
            .expect("integer overflow/underflow occurred");

        if current_sum < 0 {
            found_below_zero = true;
        }
        i = i + 1;
    }

    found_below_zero
}
// </vc-code>

fn main() {}
}