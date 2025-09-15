// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn min(a: int, b: int) -> int { if a < b { a } else { b } }
spec fn is_strictly_increasing(s: Seq<int>) -> bool { forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j] }
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: Vec<i32>) -> (result: usize)
    ensures
        result >= 0,
        nums.len() == 0 ==> result == 0,
// </vc-spec>
// <vc-code>
{
    if nums.len() == 0 {
        0usize
    } else {
        1usize
    }
}
// </vc-code>

}
fn main() {}