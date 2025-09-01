use vstd::prelude::*;

verus! {

spec fn seq_max(a: Seq<i32>) -> (ret: i32)
    decreases a.len(),
{
    if a.len() == 0 {
        i32::MIN
    } else if a.last() > seq_max(a.drop_last()) {
        a.last()
    } else {
        seq_max(a.drop_last())
    }
}

// <vc-helpers>
fn max(a: i32, b: i32) -> (ret: i32)
    ensures ret >= a && ret >= b && (ret == a || ret == b),
{
    if a > b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 <= i < numbers.len() ==> result[i] == seq_max(numbers@.take(i + 1)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut current_max: i32 = i32::MIN;
    let mut i: int = 0;

    while i < numbers.len()
        invariant
            i <= numbers.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == seq_max(numbers@.take(k + 1)),
            current_max == (if i == 0 { i32::MIN } else { seq_max(numbers@.take(i)) }),
    {
        current_max = max(current_max, numbers.tracked_borrow().raw_index(i as usize));
        result.push(current_max);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}