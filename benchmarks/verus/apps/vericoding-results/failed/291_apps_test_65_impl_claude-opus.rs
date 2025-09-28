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
/* helper modified by LLM (iteration 3): Fixed arr_to_seq to take Vec<i8> by value instead of reference */
spec fn arr_to_seq(arr: Vec<i8>) -> Seq<int> {
    arr@.map(|i: int, v: i8| v as int)
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
/* code modified by LLM (iteration 3): Fixed array indexing type issues and improved invariants */
{
    let n = arr.len();
    let mut min_val: i8 = arr[0];
    let mut min_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < n
        invariant
            1 <= i <= n,
            0 <= min_idx < i,
            min_val == arr[min_idx as int],
            forall|k: int| 0 <= k < i ==> arr@[k] as int >= min_val as int,
            forall|k: int| 0 <= k < i && arr@[k] as int == min_val as int ==> k == min_idx as int,
            min_val as int == seq_min(arr@.map(|idx: int, v: i8| v as int).subrange(0, i as int)),
    {
        if arr[i] < min_val {
            min_val = arr[i];
            min_idx = i;
        }
        i = i + 1;
    }
    
    let mut max_dist: u8 = 0;
    let mut j: usize = min_idx + 1;
    
    while j < n
        invariant
            min_idx + 1 <= j <= n,
            0 <= max_dist as int <= n - 1,
            min_val as int == seq_min(arr@.map(|idx: int, v: i8| v as int)),
            min_idx < n,
            arr[min_idx as int] == min_val,
            forall|k: int| 0 <= k < n ==> arr@[k] as int >= min_val as int,
            if max_dist > 0 {
                exists|k: int| min_idx as int < k < j as int && arr@[k] as int == min_val as int && k - min_idx as int == max_dist as int
            } else {
                forall|k: int| min_idx as int < k < j as int ==> arr@[k] as int != min_val as int
            },
            forall|k: int| min_idx as int < k < j as int && arr@[k] as int == min_val as int ==> k - min_idx as int <= max_dist as int,
    {
        if arr[j] == min_val {
            let dist = (j - min_idx) as u8;
            if dist > max_dist {
                max_dist = dist;
            }
        }
        j = j + 1;
    }
    
    if max_dist == 0 {
        let mut first_min: usize = 0;
        let mut k: usize = 0;
        
        while k < n
            invariant
                0 <= k <= n,
                if k > 0 {
                    first_min < n && arr[first_min as int] == min_val
                } else {
                    true
                },
                if k > 0 {
                    forall|m: int| 0 <= m < first_min as int ==> arr@[m] as int != min_val as int
                } else {
                    true
                },
        {
            if arr[k] == min_val {
                first_min = k;
                k = n;
            } else {
                k = k + 1;
            }
        }
        
        let mut m: usize = first_min + 1;
        
        while m < n
            invariant
                first_min + 1 <= m <= n,
                first_min < n,
                arr[first_min as int] == min_val,
                min_val as int == seq_min(arr@.map(|idx: int, v: i8| v as int)),
                if max_dist > 0 {
                    exists|p: int| first_min as int < p < m as int && arr@[p] as int == min_val as int && p - first_min as int == max_dist as int
                } else {
                    forall|p: int| first_min as int < p < m as int ==> arr@[p] as int != min_val as int
                },
        {
            if arr[m] == min_val {
                max_dist = (m - first_min) as u8;
                m = n;
            } else {
                m = m + 1;
            }
        }
    }
    
    max_dist
}
// </vc-code>


}

fn main() {}