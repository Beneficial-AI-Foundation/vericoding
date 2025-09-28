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

spec fn first_occurrence(s: Seq<int>, min_val: int, start: int, end: int) -> (result: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        start <= result <= end,
        result < end ==> s[result] == min_val,
        forall|i: int| start <= i < result ==> s[i] != min_val,
{
    if start >= end {
        end
    } else if s[start] == min_val {
        start
    } else {
        first_occurrence(s, min_val, start + 1, end)
    }
}

spec fn next_occurrence(s: Seq<int>, min_val: int, start: int, end: int) -> (result: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        start <= result <= end,
        result < end ==> s[result] == min_val,
        forall|i: int| start <= i < result ==> s[i] != min_val,
{
    if start >= end {
        end
    } else if s[start] == min_val {
        start
    } else {
        next_occurrence(s, min_val, start + 1, end)
    }
}

proof fn seq_min_non_empty(s: Seq<int>, i: int)
    requires
        s.len() > 0,
        0 <= i < s.len(),
    ensures
        seq_min(s) <= s[i],
{
    if s.len() == 1 {
        assert(seq_min(s) == s[0]);
    } else {
        let tail_min = seq_min(s.subrange(1, s.len() as int));
        assert(seq_min(s) == if s[0] <= tail_min { s[0] } else { tail_min });
        if s[0] <= tail_min {
            if i == 0 {
            } else {
                seq_min_non_empty(s.subrange(1, s.len() as int), i-1);
            }
        } else {
            seq_min_non_empty(s.subrange(1, s.len() as int), i-1);
        }
    }
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
    /* code modified by LLM (iteration 5): use usize instead of int for indices, added ghost variables */
    let ghost s = arr_to_seq(arr);
    let ghost min_val = seq_min(s);
    let mut min_distance = (arr.len() - 1) as u8;
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            min_distance > 0,
            min_distance as int <= arr.len() - 1,
            exists|k: int, l: int| 0 <= k < l < arr.len() && s[k] == s[l] && s[k] == min_val && l - k <= min_distance as int,
            forall|k: int, l: int| 0 <= k < l < i && s[k] == s[l] && s[k] == min_val ==> l - k >= min_distance as int,
    {
        if arr[i] as int == min_val {
            let j_opt = next_occurrence(s, min_val, (i + 1) as int, arr.len() as int);
            if j_opt < arr.len() as int {
                let j = j_opt as usize;
                if j - i < min_distance as usize {
                    min_distance = (j - i) as u8;
                }
            }
        }
        i = i + 1;
    }
    min_distance
}
// </vc-code>


}

fn main() {}