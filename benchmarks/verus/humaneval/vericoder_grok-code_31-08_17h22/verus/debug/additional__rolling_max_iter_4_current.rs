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
    let mut result = Vec::new();
    let mut current_max = i32::MIN;
    let n = numbers.len();
    assert(n == numbers@.len());
    for i in 0..n
        invariant
            result@.len() == i as int,
            forall|j: int| 0 <= j < i ==> result@[j] == seq_max(numbers@.take(j + 1)),
        {
            if current_max > numbers[i] {
                result.push(current_max);
            } else {
                result.push(numbers[i]);
                current_max = numbers[i];
            }
        }
    proof {
        assert(result.len() == n);
        assert(forall|i: int| 0 <= i < n ==> result@[i] == seq_max(numbers@.take(i + 1)));
    }
    result
}
// </vc-code>

fn main() {}
}