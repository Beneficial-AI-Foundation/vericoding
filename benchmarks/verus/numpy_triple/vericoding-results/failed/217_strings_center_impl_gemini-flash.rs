// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed function signature and argument type for fillchar */
fn get_padding_chars_and_lens(orig_len: int, target_width: int, fillchar: char) -> (left_pad_len: int, right_pad_len: int, fill_chars: Seq<char>)
{
    let total_pad_len = (target_width - orig_len).max(0);
    let left_pad_len = total_pad_len / 2;
    let right_pad_len = total_pad_len - left_pad_len;

    let mut fillchars_vec = Vec::new();
    let mut i = 0;
    while i < total_pad_len
        invariant
            i >= 0,
            i <= total_pad_len,
            fillchars_vec.len() == i,
            forall|j: int| 0 <= j < i ==> fillchars_vec@[j] == fillchar,
    {
        fillchars_vec.push(fillchar);
        i = i + 1;
    }
    let fillchars_seq = fillchars_vec.seq();

    (left_pad_len, right_pad_len, fillchars_seq)
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
/* code modified by LLM (iteration 5): using helper function to calculate padding characteristics */
{
    let mut result_vec: Vec<String> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            a.len() == width.len(),
            i >= 0,
            i <= a.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let orig_len = a[j]@.len() as int;
                let target_width = width[j] as int;
                &&& #[trigger] result_vec[j]@.len() >= 0
                &&& (orig_len >= target_width ==> result_vec[j] == a[j])
                &&& result_vec[j]@.len() as int == if orig_len >= target_width { orig_len } else { target_width }
            }
    {
        let s = &a[i];
        let w = width[i];

        let orig_string_len = s.len() as int;
        let target_width_int = w as int;

        if orig_string_len >= target_width_int {
            result_vec.push(s.clone());
        } else {
            let (left_pad_len, right_pad_len, fill_chars_seq) = get_padding_chars_and_lens(orig_string_len, target_width_int, fillchar);
            
            let mut new_s = String::new();
            
            proof {
                assert forall|k: int| 0 <= k < left_pad_len implies fill_chars_seq@[k] == fillchar by { /* no-op */ };
                assert forall|k: int| left_pad_len <= k < left_pad_len + right_pad_len implies fill_chars_seq@[k] == fillchar by { /* no-op */ };
            }

            new_s.push_str(&fill_chars_seq.sub(0, left_pad_len).map_values(|c| c).collect::<String>());
            new_s.push_str(s);
            new_s.push_str(&fill_chars_seq.sub(left_pad_len, left_pad_len + right_pad_len).map_values(|c| c).collect::<String>());

            result_vec.push(new_s);
        }
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}