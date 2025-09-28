// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed ghost variable declaration and increment */
fn expand_string(s: &String, tab_sz: usize) -> (result: String)
    ensures
        !result@.contains('\t'),
        (!s@.contains('\t') ==> result@ == s@),
        result@.len() >= s@.len(),
        (s@.contains('\t') ==> result@.len() > s@.len()),
{
    if !s@.contains('\t') {
        s.clone()
    } else {
        let mut result = String::new();
        let mut col: usize = 0;
        let mut char_iter = s.chars();
        ghost! { let mut i = 0; }   // ghost index

        while let Some(c) = char_iter.next()
            invariant
                0 <= i <= s@.len(),
                result@.len() >= i,
                !result@.contains('\t'),
        {
            if c == '\t' {
                let spaces_needed = tab_sz - (col % tab_sz);
                for _ in 0..spaces_needed {
                    result.push(' ');
                }
                col += spaces_needed;
            } else {
                result.push(c);
                if c == '\n' {
                    col = 0;
                } else {
                    col += 1;
                }
            }

            // Update the ghost index
            proof {
                i = i + 1;
            }
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn expandtabs(a: Vec<String>, tabsize: Vec<u8>) -> (result: Vec<String>)
    requires 
        a.len() == tabsize.len(),
        forall|i: int| 0 <= i < tabsize.len() ==> #[trigger] tabsize[i] > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            let orig_str = #[trigger] &a[i];
            let result_str = &result[i];
            let tab_sz = tabsize[i] as nat;

            (forall|c: char| #[trigger] result_str@.contains(c) ==> c != '\t') &&

            (!orig_str@.contains('\t') ==> result_str@ == orig_str@) &&

            (result_str@.len() >= orig_str@.len()) &&

            (orig_str@.contains('\t') ==> result_str@.len() > orig_str@.len())
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let orig_str = #[trigger] &a[j];
                let result_str: &String = &result[j];
                let tab_sz = tabsize[j] as nat;

                (!result_str@.contains('\t')) &&
                (!orig_str@.contains('\t') ==> result_str@ == orig_str@) &&
                (result_str@.len() >= orig_str@.len()) &&
                (orig_str@.contains('\t') ==> result_str@.len() > orig_str@.len())
            }
        decreases a.len() - i
    {
        let expanded = expand_string(&a[i], tabsize[i] as usize);
        result.push(expanded);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}