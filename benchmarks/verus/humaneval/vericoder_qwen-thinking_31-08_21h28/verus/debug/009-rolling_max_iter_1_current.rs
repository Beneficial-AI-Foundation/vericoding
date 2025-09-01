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
// pure-end

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
    let n = numbers.len();
    if n == 0 {
        return Vec::new();
    }
    let mut result = Vec::new();
    let mut current_max = numbers[0];
    result.push(current_max);
    for i in 1..n {
        invariant {
            result.len() == i
                && current_max == seq_max(numbers@.take(i))
                && forall|j: int| 0 <= j < i ==> result[j] == seq_max(numbers@.take(j+1))
        }
        if numbers[i] > current_max {
            current_max = numbers[i];
        }
        assert(seq_max(numbers@.take(i+1)) == current_max);
        result.push(current_max);
    }
    result
}
// </vc-code>

fn main() {}
}