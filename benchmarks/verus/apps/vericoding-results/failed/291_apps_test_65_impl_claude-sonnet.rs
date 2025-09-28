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

/* helper modified by LLM (iteration 5): fixed exec function to use exec types only */
exec fn arr_to_seq_exec(arr: &Vec<i8>) -> (result: Vec<i8>)
    ensures result@.len() == arr@.len(),
            forall|i: int| 0 <= i < arr@.len() ==> result@[i] == arr@[i]
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == arr@[j]
    {
        result.push(arr[i]);
        i += 1;
    }
    result
}

proof fn lemma_seq_min_in_array(s: Seq<int>)
    requires s.len() > 0
    ensures exists|i: int| 0 <= i < s.len() && s[i] == seq_min(s)
    decreases s.len()
{
    if s.len() == 1 {
        assert(s[0] == seq_min(s));
    } else {
        let tail_min = seq_min(s.subrange(1, s.len() as int));
        lemma_seq_min_in_array(s.subrange(1, s.len() as int));
        if s[0] <= tail_min {
            assert(s[0] == seq_min(s));
        } else {
            assert(exists|i: int| 1 <= i < s.len() && s[i] == tail_min);
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
    /* code modified by LLM (iteration 5): use ghost variables for spec calculations */
    ghost let seq = arr_to_seq(arr);
    let mut min_val = arr[0];
    let mut min_indices: Vec<usize> = Vec::new();
    
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            min_val as int <= seq_min(seq),
            forall|j: int| 0 <= j < i ==> min_val as int <= seq[j],
    {
        if arr[i] < min_val {
            min_val = arr[i];
            min_indices = Vec::new();
            min_indices.push(i);
        } else if arr[i] == min_val {
            min_indices.push(i);
        }
        i += 1;
    }
    
    proof {
        lemma_seq_min_in_array(seq);
    }
    
    proof {
        assert(min_val as int == seq_min(seq));
        assert(min_indices.len() >= 2);
    }
    
    let first_idx = min_indices[0];
    let second_idx = min_indices[1];
    
    let distance = (second_idx - first_idx) as u8;
    
    distance
}
// </vc-code>


}

fn main() {}