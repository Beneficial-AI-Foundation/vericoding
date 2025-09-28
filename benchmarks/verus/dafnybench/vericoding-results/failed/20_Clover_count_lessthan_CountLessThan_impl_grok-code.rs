use vstd::prelude::*;

verus! {

// <vc-helpers>
//
// Creates a sequence containing exactly the elements of the input set,
// then counts how many are less than the threshold.
// This approach leverages to_seq() to compute the count.
//
//
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count_less_than(numbers: Set<int>, threshold: int) -> (count: usize)
    ensures count == numbers.filter(|i: int| i < threshold).len()
// </vc-spec>
// <vc-code>
{
spec fn count_less_than(numbers: Set<int>, threshold: int) -> (count: usize)
    ensures count == numbers.filter(|i: int| i < threshold).len()
{
    let s = numbers.to_seq();
    let mut count: int = 0;
    let mut i: int = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count == s.take(i).filter(#[trigger] |val: int| val < threshold).len(),
    {
        if s.index(i) < threshold {
            count += 1;
        }
        i += 1;
    }
    // Assert the final count matches the specification
    assert(count == numbers.filter(#[trigger] |x: int| x < threshold).len());
    count as usize
}
}
// </vc-code>

fn main() {}

}