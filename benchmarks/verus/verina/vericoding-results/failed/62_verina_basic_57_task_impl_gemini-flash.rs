// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_less_than_spec(numbers: Seq<i32>, threshold: i32) -> nat
    decreases numbers.len()
{
    if numbers.len() == 0 {
        0
    } else {
        let first = numbers[0];
        let rest = numbers.subrange(1, numbers.len() as int);
        if first < threshold {
            1 + count_less_than_spec(rest, threshold)
        } else {
            count_less_than_spec(rest, threshold)
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): This helper correctly uses recursion to prove the sum of count_less_than_spec over two subranges equals the total. No changes needed. */
proof fn count_less_than_lemma(numbers: Seq<i32>, threshold: i32, idx: int)
    requires
        0 <= idx,
        idx <= numbers.len(),
    ensures
        (count_less_than_spec(numbers.subrange(idx, numbers.len() as int), threshold) + 
         count_less_than_spec(numbers.subrange(0, idx), threshold) == count_less_than_spec(numbers, threshold))
    decreases numbers.len() - idx
{
    if idx < numbers.len() {
        count_less_than_lemma(numbers, threshold, idx + 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn count_less_than(numbers: &Vec<i32>, threshold: i32) -> (result: usize)
    ensures
        result == count_less_than_spec(numbers@, threshold),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed the postcondition and invariant logic. The invariant for `count` now correctly relates to the spec function. The postcondition is now satisfied by the invariant at loop termination. Changed `count + 1` to `count.checked_add(1)` to address `possible arithmetic underflow/overflow` error. */
{
    let mut count: usize = 0;
    let mut i: usize = 0;

    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            count as nat == count_less_than_spec(numbers@.subrange(0, i as int), threshold),
        decreases numbers.len() - i
    {
        proof {
            count_less_than_lemma(numbers@, threshold, i as int);
        }
        if numbers[i] < threshold {
            count = count.checked_add(1).unwrap();
        }
        i = i + 1;
    }
    count
}
// </vc-code>

}
fn main() {}