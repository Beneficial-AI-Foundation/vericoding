// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed function return type syntax */
proof fn compute_padding(orig_len: int, target_width: int) -> (int, int)
    requires
        orig_len >= 0,
        target_width >= 0,
        orig_len <= target_width,
    ensures
        left_pad + orig_len + right_pad == target_width,
        left_pad >= 0,
        right_pad >= 0,
        (left_pad - right_pad) == 0 || (left_pad - right_pad) == 1 || (right_pad - left_pad) == 1
{
    let total_padding = target_width - orig_len;
    let left_pad = total_padding / 2;
    let right_pad = total_padding - left_pad;
    (left_pad, right_pad)
}
fn make_padding_string(len: usize, fillchar: char) -> (s: String)
    ensures
        s@.len() == len
{
    let mut result = String::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result@.len() == i,
    {
        result.push(fillchar);
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn center(a: Vec<String>, width: Vec<usize>, fillchar: char) -> (result: Vec<String>)
    requires 
        a.len() == width.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i]@.len() >= 0 && {
                let orig_len = a[i]@.len() as int;
                let target_width = width[i] as int;
                &&& (orig_len >= target_width ==> result[i] == a[i])
                &&& result[i]@.len() as int == if orig_len >= target_width { orig_len } else { target_width }
            }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error in padding function signature */
    let mut result_vec = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let orig_len = a[j]@.len() as int;
                let target_width = width[j] as int;
                &&& (orig_len >= target_width ==> result_vec[j] == a[j])
                &&& result_vec[j]@.len() == (if orig_len >= target_width { orig_len } else { target_width }) as usize
            }
    {
        let orig_string = a.index(i).clone();
        let target_width_val = *width.index(i);
        
        if orig_string@.len() >= target_width_val {
            result_vec.push(orig_string);
        } else {
            proof {
                let orig_len_int = orig_string@.len() as int;
                let target_width_int = target_width_val as int;
                let (left_pad, right_pad) = compute_padding(orig_len_int, target_width_int);
                assert(left_pad >= 0);
                assert(right_pad >= 0);
                assert(left_pad + orig_len_int + right_pad == target_width_int);
            }
            
            let total_padding = target_width_val - orig_string@.len();
            let left_pad_len = total_padding / 2;
            let right_pad_len = total_padding - left_pad_len;
            
            let left_padding = make_padding_string(left_pad_len, fillchar);
            let right_padding = make_padding_string(right_pad_len, fillchar);
            
            let mut centered_string = String::new();
            centered_string.push_str(&left_padding);
            centered_string.push_str(&orig_string);
            centered_string.push_str(&right_padding);
            
            result_vec.push(centered_string);
        }
        
        i += 1;
    }
    
    result_vec
}
// </vc-code>

}
fn main() {}