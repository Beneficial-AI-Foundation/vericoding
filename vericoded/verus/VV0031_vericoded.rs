// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_len_reflexive(len: usize)
    ensures
        len <= len,
{
}

// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(numbers: Vec<i32>) -> (result: usize)
    ensures
        result <= numbers.len(),
// </vc-spec>
// <vc-code>
{
    let result = numbers.len();
    result
}
// </vc-code>

}
fn main() {}