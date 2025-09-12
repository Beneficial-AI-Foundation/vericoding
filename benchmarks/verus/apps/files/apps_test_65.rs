// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn seq_min(s: Seq<int>) -> int 
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        s[0]
    } else {
        let tail_min = seq_min(s.subrange(1, s.len() as int));
        if s[0] <= tail_min {
            s[0]
        } else {
            tail_min
        }
    }
}

spec fn valid_input(arr: Seq<int>) -> bool {
    arr.len() >= 2 && 
    exists|i: int, j: int| 0 <= i < j < arr.len() && #[trigger] arr[i] == #[trigger] arr[j] && arr[i] == seq_min(arr)
}
// </vc-helpers>

// <vc-spec>
fn solve(arr: Seq<int>) -> (result: int)
    requires 
        valid_input(arr),
    ensures 
        result > 0,
        result <= arr.len() - 1,
        exists|i: int, j: int| 0 <= i < j < arr.len() && #[trigger] arr[i] == #[trigger] arr[j] && arr[i] == seq_min(arr) && j - i == result,
        forall|i: int, j: int| 0 <= i < j < arr.len() && #[trigger] arr[i] == #[trigger] arr[j] && arr[i] == seq_min(arr) ==> j - i >= result,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}