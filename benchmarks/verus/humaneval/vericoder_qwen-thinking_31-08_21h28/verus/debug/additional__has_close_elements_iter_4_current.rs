use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}

// <vc-helpers>
#[verifier::loop_isolation(false)]
fn sort_sequence(seq: Seq<i32>) -> Seq<i32> {
    let mut result = Seq::new();
    for i in 0..seq.len() {
        let elem = seq@[i];
        let mut j = 0;
        while j < result.len() {
            invariant(0 <= j && j <= result.len());
            invariant(forall |k: int| 0 <= k && k < j implies elem >= result@[k]);
            if elem < result@[j] {
                break;
            }
            j = j + 1;
        }
        result = result[..j] + [elem] + result[j..];
    }
    result
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn has_close_elements(numbers: &[i32], threshold: i32) -> (flag: bool)
    // pre-conditions-start
    requires
        threshold > 0,
        forall|i: int, j: int| 0 <= i && i < numbers.len() && 0 <= j && j < numbers.len() ==> numbers[i] - numbers[j] < i32::MAX && -(numbers[i] - numbers[j]) < i32::MAX
    // pre-conditions-end
    // post-conditions-start
    ensures
        flag == exists|i: int, j: int| 0 <= i && 0 <= j && i < numbers.len() && j < numbers.len() && i != j && abs_spec(numbers[i] - numbers[j]) < threshold
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if numbers.len() < 2 {
        return false;
    }
    let n = numbers.len();
    let sorted_seq = numbers.to_seq();
    let sorted_seq = sort_sequence(sorted_seq);
    let mut i = 0;
    while i < n - 1 {
        invariant(forall |j: usize| 0 <= j && j < i ==> sorted_seq@[j+1] - sorted_seq@[j] >= threshold);
        if sorted_seq@[i+1] - sorted_seq@[i] < threshold {
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-code>

fn main() {}
}