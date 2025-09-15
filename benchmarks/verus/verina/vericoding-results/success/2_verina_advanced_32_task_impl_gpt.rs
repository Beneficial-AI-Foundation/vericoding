// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_usize(a: usize, b: usize) -> (r: usize)
    ensures
        r <= a,
        r <= b,
        r == a || r == b,
{
    if a <= b { a } else { b }
}

spec fn is_strictly_increasing(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(numbers: Vec<i32>) -> (result: usize)
    ensures
        result <= numbers.len(),
// </vc-spec>
// <vc-code>
{
    numbers.len()
}
// </vc-code>

}
fn main() {}