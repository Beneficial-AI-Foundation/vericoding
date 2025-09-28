// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn split(a: Vec<String>, sep: String, maxsplit: Option<usize>) -> (result: Vec<Vec<String>>)
    requires
        sep@ != Seq::<char>::empty(),
        a.len() > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() as int ==> {
            let parts = #[trigger] result[i]@;
            let original = #[trigger] a[i]@;
            (forall|j: int| 0 <= j < parts.len() as int ==> parts[j]@ != sep@) &&
            (match maxsplit {
                None => true,
                Some(limit) => parts.len() <= limit + 1,
            }) &&
            parts.len() >= 1 &&
            (original.len() == 0 ==> parts.len() == 1 && parts[0]@.len() == 0) &&
            (original == sep@ ==> parts.len() == 2 && parts[0]@.len() == 0 && parts[1]@.len() == 0)
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Changed casting from `as nat` to `as int` for `subsequence` arguments within executable code, as `nat` is for ghost code. */
    let mut result: Vec<Vec<String>> = Vec::new();
    let sep_len = sep.len();

    for i in 0..a.len() {
        let s = &a[i];
        let s_seq = s@;
        let sep_seq = sep@;
        let mut current_parts: Vec<String> = Vec::new();
        let mut start_idx = 0usize;
        let mut splits_made = 0usize;

        if s.is_empty() {
            current_parts.push(String::new());
            result.push(current_parts);
            continue;
        }

        while start_idx < s_seq.len()
            invariant
                current_parts.len() <= splits_made + 1,
                start_idx <= s_seq.len(),
                forall|k: int| 0 <= k < current_parts.len() as int ==> current_parts[k]@ != sep_seq,
                s_seq.len() > 0 ==> current_parts.len() >= 0,
        {
            let mut found_sep = false;
            let mut end_of_segment = s_seq.len();

            if maxsplit.is_some() && splits_made >= maxsplit.unwrap() {
                break;
            }
            
            let mut j = start_idx;
            while j <= s_seq.len().checked_sub(sep_len).unwrap_or(0)
                invariant
                    start_idx <= j,
                    j <= s_seq.len().checked_sub(sep_len).unwrap_or(0) + 1,
                    !found_sep,
            {
                if s_seq.subsequence(j as int, (j + sep_len) as int) == sep_seq {
                    found_sep = true;
                    end_of_segment = j;
                    break;
                }
                j = j.checked_add(1).unwrap_or(j);
            }

            if found_sep {
                current_parts.push(s_seq.subsequence(start_idx as int, end_of_segment as int).to_string());
                start_idx = end_of_segment + sep_len;
                splits_made = splits_made.checked_add(1).unwrap_or(splits_made);
            } else {
                break;
            }
        }
        current_parts.push(s_seq.subsequence(start_idx as int, s_seq.len() as int).to_string());
        result.push(current_parts);
    }
    result
}
// </vc-code>


}
fn main() {}