use vstd::prelude::*;

verus! {

spec fn isMax(m: int, numbers: Seq<int>) -> bool {
    numbers.contains(m) &&
    forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= m
}

// <vc-helpers>
// Helper proofs or code can be added here if needed for verification.
// In this case, no additional helpers are required.
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<int>) -> (result: Vec<int>)
    requires
        numbers.len() > 0,
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 < i < result.len() ==> isMax(result[i], numbers@.subrange(0, i + 1)),
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<int> = Vec::new();
    result.push(numbers[0]);
    proof {
        assert(result@[0] == numbers@[0]);
        let seq = numbers@.subrange(0, 1);
        assert(seq.len() == 1);
        assert(seq@[0] == numbers@[0]);
        assert(seq.contains(numbers@[0]));
        assert(forall|j: int| 0 <= j < seq.len() ==> #[trigger] seq@[j] <= numbers@[0]);
        assert(isMax(result@[0], numbers@.subrange(0, 1)));
    }
    let mut current_max = numbers[0];
    let mut i: usize = 1;
    while i < numbers.len()
        invariant
            i <= numbers@.len(),
            result.len() as int == i,
            current_max == result@[i - 1],
            forall|k: int| 0 <= k < i ==> #[trigger] isMax(result@[k], numbers@.subrange(0, k + 1)),
            forall|j: int| 0 <= j < i ==> #[trigger] numbers@[j] <= current_max
    {
        let element = numbers[i];
        let new_max = if current_max >= element { current_max } else { element };
        proof {
            assert(new_max >= current_max);
            assert(new_max >= numbers@[i]);
            assert(forall|j: int| 0 <= j <= i ==> #[trigger] (numbers@[j] <= new_max) by {
                if j < i {
                    assert(numbers@[j] <= current_max) by (invariant);
                    assert(current_max <= new_max);
                } else {
                    assert(j == i);
                    assert(new_max >= numbers@[i]);
                }
            });
            assert(numbers@.subrange(0, i + 1).contains(new_max)) by {
                if new_max == current_max {
                    assert(i >= 1);
                    assert(current_max == result@[i - 1]);
                    assert(isMax(current_max, numbers@.subrange(0, i))) by (invariant);
                    assert(numbers@.subrange(0, i).contains(current_max));
                } else {
                    assert(new_max == numbers@[i]);
                }
            };
        }
        result.push(new_max);
        current_max = new_max;
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}