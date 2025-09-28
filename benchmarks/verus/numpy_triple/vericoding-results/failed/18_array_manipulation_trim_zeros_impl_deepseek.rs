// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Represents the trim mode for trim_zeros function */
#[derive(Eq, PartialEq)]
pub enum TrimMode {
    /* Trim zeros from the front of the array only (corresponds to 'f') */
    Front,
    /* Trim zeros from the back of the array only (corresponds to 'b') */
    Back,
    /* Trim zeros from both front and back of the array (corresponds to 'fb', default) */
    Both,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed scope and type issues in spec functions */
#[verifier::spec]
spec fn find_first_non_zero(s: Seq<f32>) -> (idx: int)
    recommends
        0 <= idx,
        idx <= s.len()
    ensures
        forall|i: int| 0 <= i < idx ==> s[i] == 0.0f32,
        idx == s.len() || s[idx] != 0.0f32
{
    if s.len() == 0 {
        0
    } else if s[0] != 0.0f32 {
        0
    } else {
        1 + find_first_non_zero(s.subrange(1, s.len()))
    }
}

#[verifier::spec]
spec fn find_last_non_zero(s: Seq<f32>) -> (idx: int)
    recommends
        -1 <= idx,
        idx < s.len()
    ensures
        forall|i: int| idx < i < s.len() ==> s[i] == 0.0f32,
        idx == -1 || s[idx] != 0.0f32
{
    if s.len() == 0 {
        -1
    } else if s[s.len() - 1] != 0.0f32 {
        s.len() as int - 1
    } else {
        find_last_non_zero(s.subrange(0, s.len() - 1))
    }
}

proof fn slice_contains_original_elements(s: Seq<f32>, start: int, end: int)
    requires
        0 <= start <= end <= s.len()
    ensures
        forall|i: int| 0 <= i < end - start ==> 
            exists|j: int| 0 <= j < s.len() && s.subrange(start, end)[i] == s[j]
{
}
// </vc-helpers>

// <vc-spec>
fn trim_zeros(arr: Vec<f32>, mode: TrimMode) -> (result: Vec<f32>)
    ensures
        result@.len() <= arr@.len(),
        /* Result contains only elements from the original array */
        forall|i: int| 0 <= i < result@.len() ==> 
            exists|j: int| 0 <= j < arr@.len() && #[trigger] result@[i] == arr@[j],
        /* Basic trimming properties based on mode */
        (mode == TrimMode::Front ==> 
            (result@.len() == 0 || result@[0] != 0.0f32)),
        (mode == TrimMode::Back ==> 
            (result@.len() == 0 || result@[result@.len() - 1] != 0.0f32)),
        (mode == TrimMode::Both ==> 
            (result@.len() == 0 || (result@[0] != 0.0f32 && result@[result@.len() - 1] != 0.0f32)))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed variable scoping and added ghost code */
{
    if arr.is_empty() {
        return Vec::new();
    }
    
    let s = arr@;
    let mut start = 0;
    let mut end = s.len();
    
    proof {
        let first_non_zero = find_first_non_zero(s);
        let last_non_zero = find_last_non_zero(s);
        
        if mode == TrimMode::Front || mode == TrimMode::Both {
            start = first_non_zero;
        }
        if mode == TrimMode::Back || mode == TrimMode::Both {
            end = if last_non_zero == -1 { 0 } else { last_non_zero + 1 };
        }
        
        if start <= end {
            slice_contains_original_elements(s, start, end);
        }
    }
    
    if start >= end {
        Vec::new()
    } else {
        let mut result = Vec::new();
        let mut index = start;
        while index < end
            invariant
                index <= end,
                result@.len() == index - start
        {
            result.push(arr[index as usize]);
            index = index + 1;
        }
        result
    }
}
// </vc-code>


}
fn main() {}