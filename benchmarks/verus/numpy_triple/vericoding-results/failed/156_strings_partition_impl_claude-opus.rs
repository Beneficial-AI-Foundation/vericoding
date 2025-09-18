// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn find_separator_index(s: Seq<char>, sep: Seq<char>) -> int
    decreases s.len()
{
    if sep.len() == 0 || s.len() < sep.len() {
        -1
    } else if s.subrange(0, sep.len() as int) == sep {
        0
    } else {
        let rest = find_separator_index(s.subrange(1, s.len() as int), sep);
        if rest == -1 { -1 } else { rest + 1 }
    }
}

proof fn find_separator_index_properties(s: Seq<char>, sep: Seq<char>)
    ensures
        find_separator_index(s, sep) == -1 || (0 <= find_separator_index(s, sep) <= s.len() - sep.len()),
        find_separator_index(s, sep) >= 0 ==> s.subrange(find_separator_index(s, sep), find_separator_index(s, sep) + sep.len() as int) == sep,
    decreases s.len()
{
    if sep.len() == 0 || s.len() < sep.len() {
    } else if s.subrange(0, sep.len() as int) == sep {
    } else {
        if s.len() > 1 {
            find_separator_index_properties(s.subrange(1, s.len() as int), sep);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn partition(a: Vec<String>, sep: String) -> (result: (Vec<String>, Vec<String>, Vec<String>))
    ensures
        result.0.len() == a.len() && result.1.len() == a.len() && result.2.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            let original = #[trigger] a[i]@;
            let before_i = result.0[i]@;
            let sep_i = result.1[i]@;
            let after_i = result.2[i]@;

            before_i + sep_i + after_i == original &&

            (sep_i == sep@ || sep_i.len() == 0) &&

            (sep_i.len() == 0 ==> after_i.len() == 0 && before_i == original) &&

            original.len() == before_i.len() + sep_i.len() + after_i.len()
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed numeric literals - removed invalid suffixes */
    let mut result_before: Vec<String> = Vec::new();
    let mut result_sep: Vec<String> = Vec::new();
    let mut result_after: Vec<String> = Vec::new();

    let sep_seq = sep@;
    
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result_before.len() == i,
            result_sep.len() == i,
            result_after.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let original = #[trigger] a[j]@;
                let before_j = result_before[j]@;
                let sep_j = result_sep[j]@;
                let after_j = result_after[j]@;
                
                before_j + sep_j + after_j == original &&
                (sep_j == sep_seq || sep_j.len() == 0) &&
                (sep_j.len() == 0 ==> after_j.len() == 0 && before_j == original) &&
                original.len() == before_j.len() + sep_j.len() + after_j.len()
            },
    {
        let current = &a[i];
        let current_seq = current@;
        
        let idx = find_separator_index(current_seq, sep_seq);
        proof {
            find_separator_index_properties(current_seq, sep_seq);
        }
        
        if idx >= 0 && sep_seq.len() > 0 {
            let idx_usize = idx as usize;
            let sep_len = sep_seq.len() as usize;
            let end_idx = idx_usize + sep_len;
            
            let before_str = current.substring_char(0, idx_usize);
            let sep_str = current.substring_char(idx_usize, end_idx);
            let after_str = current.substring_char(end_idx, current.len());
            
            result_before.push(before_str.to_string());
            result_sep.push(sep_str.to_string());
            result_after.push(after_str.to_string());
        } else {
            result_before.push(current.clone());
            result_sep.push(String::new());
            result_after.push(String::new());
        }
        
        i = i + 1;
    }
    
    (result_before, result_sep, result_after)
}
// </vc-code>

}
fn main() {}