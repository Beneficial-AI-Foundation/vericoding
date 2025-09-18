// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains_tab(s: &str) -> bool {
    s@.contains('\t')
}
// </vc-helpers>

// <vc-spec>
fn expandtabs(a: Vec<String>, tabsize: Vec<usize>) -> (result: Vec<String>)
    requires 
        a.len() == tabsize.len(),
        forall|i: int| 0 <= i < tabsize.len() ==> tabsize[i] > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
            let orig_str = &a[i];
            let result_str = &result[i];
            let tab_sz = tabsize[i];

            (forall|c: char| result_str@.contains(c) ==> c != '\t') &&

            (!orig_str@.contains('\t') ==> result_str@ == orig_str@) &&

            (result_str@.len() >= orig_str@.len()) &&

            (orig_str@.contains('\t') ==> result_str@.len() > orig_str@.len())
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed int type usage by using usize and iterator-based loops */
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < a.len()
        invariant
            0 <= i as int <= a.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                let orig_str = &a[j as usize];
                let result_str: &String = &result[j as usize];
                let tab_sz = tabsize[j as usize];

                (!result_str@.contains('\t')) &&
                (!orig_str@.contains('\t') ==> result_str@ == orig_str@) &&
                (result_str@.len() >= orig_str@.len()) &&
                (orig_str@.contains('\t') ==> result_str@.len() > orig_str@.len())
            }
    {
        let s = &a[i];
        let tab_sz = tabsize[i];
        let mut has_tab = false;
        for c in s.chars() {
            if c == '\t' {
                has_tab = true;
                break;
            }
        }
        let expanded = if !has_tab {
            s.clone()
        } else {
            let mut expanded_str = String::new();
            let mut current_column = 0usize;
            for c in s.chars() {
                if c == '\t' {
                    let spaces_to_add = tab_sz - (current_column % tab_sz);
                    for _ in 0..spaces_to_add {
                        expanded_str.push(' ');
                    }
                    current_column += spaces_to_add;
                } else {
                    expanded_str.push(c);
                    current_column += 1;
                }
            }
            expanded_str
        };
        result.push(expanded);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}