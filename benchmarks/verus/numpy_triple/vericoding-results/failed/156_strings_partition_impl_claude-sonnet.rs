// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type compatibility with nat */
spec fn string_contains_at(s: Seq<char>, sep: Seq<char>, pos: int) -> bool
    requires pos >= 0
{
    pos + sep.len() <= s.len() &&
    forall|i: int| 0 <= i < sep.len() ==> s[pos + i] == sep[i]
}

fn split_at_first_occurrence(s: String, sep: String) -> (String, String, String)
    ensures
        ({ let (before, sep_part, after) = split_at_first_occurrence(s, sep); before@ + sep_part@ + after@ == s@ }),
        ({ let (before, sep_part, after) = split_at_first_occurrence(s, sep); sep_part@ == sep@ || sep_part@.len() == 0 }),
        ({ let (before, sep_part, after) = split_at_first_occurrence(s, sep); sep_part@.len() == 0 ==> after@.len() == 0 && before@ == s@ })
{
    let s_seq = s@;
    let sep_seq = sep@;
    
    if sep_seq.len() == 0nat {
        return (s, String::new(), String::new());
    }
    
    let mut pos: usize = 0;
    while pos + sep_seq.len() <= s_seq.len()
        invariant pos >= 0
    {
        let mut found = true;
        let mut i: usize = 0;
        while i < sep_seq.len()
            invariant
                0 <= i <= sep_seq.len(),
                found == forall|j: int| 0 <= j < i ==> s_seq@[pos + j] == sep_seq@[j]
        {
            if pos + i >= s_seq.len() || s_seq@[pos + i] != sep_seq@[i] {
                found = false;
                break;
            }
            i = i + 1;
        }
        
        if found {
            let before_str = s.substring_char(0, pos);
            let after_str = s.substring_char(pos + sep_seq.len(), s_seq.len());
            return (before_str, sep, after_str);
        }
        pos = pos + 1;
    }
    
    (s, String::new(), String::new())
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
/* code modified by LLM (iteration 5): main partition implementation */
{
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
                (sep_j.len() == 0 ==> after_j.len() == 0 && before_j == original)
            }
    {
        let (before, sep_part, after) = split_at_first_occurrence(a[i].clone(), sep.clone());
        result_before.push(before);
        result_sep.push(sep_part);
        result_after.push(after);
        i = i + 1;
    }
    
    (result_before, result_sep, result_after)
}
// </vc-code>

}
fn main() {}