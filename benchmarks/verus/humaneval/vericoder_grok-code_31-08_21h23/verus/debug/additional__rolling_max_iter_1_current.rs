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
spec fn int_max(a: i32, b: i32) -> i32 {
    if a >= b { a } else { b }
}

#[verifier(external_body)]
pub proof fn lemma_seq_max_append(s: Seq<i32>, b: i32) 
    ensures 
        seq_max(s + seq![b]) == (if s.len() == 0 { b } else { int_max(seq_max(s), b) })
{
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
    let mut result = Vec::with_capacity(numbers.len());
    let mut current_max = i32::MIN;
    for i in 0..numbers.len()
        invariant
            0 <= i <= numbers.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == seq_max(numbers@.take(j + 1)),
            i == 0 ==> current_max == i32::MIN,
            0 < i ==> current_max == seq_max(numbers@.take(i))
    {
        let next = numbers[i];
        if i == 0 {
            current_max = next;
            assert(current_max == seq_max(numbers@.take(1)));
        } else {
            assert(current_max == seq_max(numbers@.take(i)));
            current_max = if next > current_max { next } else { current_max };
            assert(seq_max(numbers@.take(i + 1)) == int_max(seq_max(numbers@.take(i)), next));
            assert(current_max == seq_max(numbers@.take(i + 1)));
        }
        result.push(current_max);
    }
    result
}
// </vc-code>

fn main() {}
}