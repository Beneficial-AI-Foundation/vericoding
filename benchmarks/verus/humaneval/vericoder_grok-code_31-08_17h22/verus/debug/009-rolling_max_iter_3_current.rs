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
proof fn lemma_seq_max_take_update(x: Seq<i32>, i: int)
    requires
        0 <= i < x.len(),
    ensures
        seq_max(x.take(i + 1)) == if x[i] > seq_max(x.take(i)) { x[i] } else { seq_max(x.take(i)) },
{
    let take_i = x.take(i);
    let take_ip1 = x.take(i + 1);
    assert(take_ip1 == take_i + seq![x[i]]);
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
    let mut result = Vec::new();
    let mut current_max = i32::MIN;
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i as int <= numbers@.len(),
            result@.len() == i as int,
            current_max == seq_max(numbers@.take(i as int)),
            forall |j: int| 0 <= j < i as int ==> result@[j] == seq_max(numbers@.take(j + 1)),
    {
        let new_val = numbers[i];
        let new_max = if new_val > current_max { new_val } else { current_max };
        proof {
            assert(new_val == numbers@[i as int]);
            lemma_seq_max_take_update(numbers@, i as int);
            assert(new_max == seq_max(numbers@.take((i as int) + 1)));
        }
        result.push(new_max);
        current_max = new_max;
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}