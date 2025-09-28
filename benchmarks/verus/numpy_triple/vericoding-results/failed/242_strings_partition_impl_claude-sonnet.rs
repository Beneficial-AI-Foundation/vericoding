// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): moved index operations into proof blocks to fix ghost code restrictions */
fn find_separator_position(s: &String, sep: &String) -> (pos: Option<usize>)
    ensures
        match pos {
            Some(i) => i as int + sep@.len() <= s@.len() && s@.subrange(i as int, i as int + sep@.len()) == sep@,
            None => forall|j: int| 0 <= j <= s@.len() - sep@.len() ==> s@.subrange(j, j + sep@.len()) != sep@
        }
{
    if sep@.len() == 0nat {
        return None;
    }
    
    let mut i = 0;
    while i + sep.len() <= s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i && j + sep@.len() <= s@.len() ==> s@.subrange(j, j + sep@.len()) != sep@
    {
        let mut found = true;
        let mut k = 0;
        while k < sep.len()
            invariant
                0 <= k <= sep.len(),
                found == (forall|m: int| 0 <= m < k ==> s@.index((i + m) as int) == sep@.index(m as int))
        {
            proof {
                if s@.index((i + k) as int) != sep@.index(k as int) {
                    found = false;
                }
            }
            if s.as_bytes()[i + k] != sep.as_bytes()[k] {
                found = false;
                break;
            }
            k += 1;
        }
        if found {
            return Some(i);
        }
        i += 1;
    }
    None
}
// </vc-helpers>

// <vc-spec>
fn partition(a: Vec<String>, sep: String) -> (result: (Vec<String>, Vec<String>, Vec<String>))
    ensures
        result.0.len() == a.len() && result.1.len() == a.len() && result.2.len() == a.len(),
        forall|i: int| 0 <= i < a.len() as int ==> {
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
    /* code modified by LLM (iteration 5): maintained proof block structure for type safety */
    let mut result_before: Vec<String> = Vec::new();
    let mut result_sep: Vec<String> = Vec::new();
    let mut result_after: Vec<String> = Vec::new();
    
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result_before.len() == i,
            result_sep.len() == i,
            result_after.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let original = a[j]@;
                let before_j = result_before[j]@;
                let sep_j = result_sep[j]@;
                let after_j = result_after[j]@;
                before_j + sep_j + after_j == original &&
                (sep_j == sep@ || sep_j.len() == 0) &&
                (sep_j.len() == 0 ==> after_j.len() == 0 && before_j == original) &&
                original.len() == before_j.len() + sep_j.len() + after_j.len()
            }
    {
        let current_string = &a[i];
        let sep_pos = find_separator_position(current_string, &sep);
        
        match sep_pos {
            Some(pos) => {
                let before_part = current_string.substring_char(0, pos).to_string();
                let after_start = pos + sep.len();
                let after_part = current_string.substring_char(after_start, current_string.len()).to_string();
                
                result_before.push(before_part);
                result_sep.push(sep.clone());
                result_after.push(after_part);
            },
            None => {
                result_before.push(current_string.clone());
                result_sep.push(String::new());
                result_after.push(String::new());
            }
        }
        i += 1;
    }
    
    (result_before, result_sep, result_after)
}
// </vc-code>

}
fn main() {}