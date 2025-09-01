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
    let mut res = Vec::new();
    let mut cur_max = i32::MIN;
    let mut i = 0;
    while i < numbers.len()
        decreases numbers.len() - i
        invariant i <= numbers.len() && res.len() == i && cur_max == seq_max(numbers@.take(i))
    {
        if numbers[i] > cur_max {
            cur_max = numbers[i];
        }
        res.push(cur_max);
        i += 1;
    }
    res
}
// </vc-code>

fn main() {}
}