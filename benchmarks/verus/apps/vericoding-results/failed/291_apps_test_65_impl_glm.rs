// <vc-preamble>
use vstd::prelude::*;

verus! {
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
// </vc-preamble>

// <vc-helpers>
spec fn arr_to_seq(arr: Vec<i8>) -> Seq<int> {
    arr@.map(|i, v| v as int)
}
// </vc-helpers>

// <vc-spec>
fn solve(arr: Vec<i8>) -> (result: u8)
    requires 
        valid_input(arr_to_seq(arr)),
    ensures 
        result > 0,
        result as int <= arr.len() - 1,
        exists|i: int, j: int| 0 <= i < j < arr.len() && #[trigger] arr_to_seq(arr)[i] == #[trigger] arr_to_seq(arr)[j] && arr_to_seq(arr)[i] == seq_min(arr_to_seq(arr)) && j - i == result as int,
        forall|i: int, j: int| 0 <= i < j < arr.len() && #[trigger] arr_to_seq(arr)[i] == #[trigger] arr_to_seq(arr)[j] && arr_to_seq(arr)[i] == seq_min(arr_to_seq(arr)) ==> j - i >= result as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed overflow by using u8 for min_diff and added array length assertion */
    assert(arr.len() <= 256);
    let mut min_val = arr[0];
    for i in 1..arr.len() {
        if arr[i] < min_val {
            min_val = arr[i];
        }
    }

    let mut last_index: Option<usize> = None;
    let mut min_diff: u8 = 255;

    for i in 0..arr.len() {
        if arr[i] == min_val {
            if let Some(last) = last_index {
                let diff = (i - last) as u8;
                if diff < min_diff {
                    min_diff = diff;
                }
            }
            last_index = Some(i);
        }
    }

    min_diff
}
// </vc-code>


}

fn main() {}