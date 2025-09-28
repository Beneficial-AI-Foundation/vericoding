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
/* helper modified by LLM (iteration 5): Fixed type mismatches in invariants by using arr@ indexing with int and proper casting */
spec fn arr_to_seq(arr: Vec<i8>) -> Seq<int> {
    arr@.map(|i, v| v as int)
}

exec fn find_array_min(arr: &Vec<i8>) -> (result: i8)
    requires
        arr.len() >= 1,
    ensures
        forall |k: int| 0 <= k < arr@.len() ==> (arr@[k] as int) >= (result as int),
        exists |k: int| 0 <= k < arr@.len() && (arr@[k] as int) == (result as int),
{
    let mut min_val = arr[0];
    let mut i = 1;
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            min_val <= arr[0],
            (forall|k: int| 0 <= k < i ==> arr[k] >= min_val),
        decreases arr.len() - i,
    {
        if arr[i] < min_val {
            min_val = arr[i];
        }
        i = i + 1;
    }
    min_val
}

exec fn find_min_distance(arr: &Vec<i8>, min_val: i8) -> (result: u8)
    requires
        arr.len() >= 2,
        exists|i: int, j: int| 0 <= i < j < arr.len() && arr[i] == min_val && arr[j] == min_val,
    ensures
        result > 0,
        result as int <= (arr.len() as int) - 1,
        exists|i: int, j: int| 0 <= i < j < arr@.len() && arr@[i] == (min_val as int) && arr@[j] == (min_val as int) && j - i == result as int,
        forall|i: int, j: int| 0 <= i < j < arr@.len() && arr@[i] == (min_val as int) && arr@[j] == (min_val as int) ==> j - i >= result as int,
{
    let mut first_index = 0;
    let mut prev_index = 0;
    let mut min_dist = u8::MAX;
    let mut found_first = false;
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            !found_first ==> exists|k: int| (i as int) <= k < arr@.len() && arr@[k] == (min_val as int),
            found_first ==> arr@[prev_index as int] == (min_val as int),
            found_first && (prev_index as int) < (i as int) && arr@[prev_index as int] == (min_val as int) ==> (forall|k: int| (prev_index as int) < k < (i as int) ==> arr@[k] != (min_val as int)),
            min_dist != u8::MAX ==> min_dist as int >= 1,
            min_dist != u8::MAX ==> exists|p: int, q: int| 0 <= p < q < (i as int) && arr@[p] == (min_val as int) && arr@[q] == (min_val as int) && (q - p) == min_dist as int,
        decreases arr.len() - i,
    {
        if arr[i] == min_val {
            if !found_first {
                first_index = i;
                prev_index = i;
                found_first = true;
            } else {
                let dist = (i - prev_index) as u8;
                if dist < min_dist {
                    min_dist = dist;
                }
                prev_index = i;
            }
        }
        i = i + 1;
    }
    min_dist
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
/* code modified by LLM (iteration 5): Kept implementation as it calls the fixed helpers */
{
    let min_val = find_array_min(&arr);
    let result = find_min_distance(&arr, min_val);
    result
}
// </vc-code>


}

fn main() {}