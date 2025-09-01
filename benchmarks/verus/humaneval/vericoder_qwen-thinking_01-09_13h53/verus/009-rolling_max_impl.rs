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
    if numbers.len() == 0 {
        return Vec::new();
    }
    let mut result = Vec::new();
    result.push(numbers[0]);
    let mut i: usize = 1;
    while i < numbers.len() {
        invariant { i >= 1 && result.len() == i && result[(i-1)] == seq_max(numbers@.take(i)) };
        let new_max = if result[(i-1)] > numbers[i] { result[(i-1)] } else { numbers[i] };
        result.push(new_max);
        i = i + 1;
    }
    return result;
}
// </vc-code>

fn main() {}
}