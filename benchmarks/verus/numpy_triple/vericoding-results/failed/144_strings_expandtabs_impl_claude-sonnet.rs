// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove int cast and use ghost operations */
fn expand_single_string(s: &String, tab_size: usize) -> (result: String)
    requires tab_size > 0
    ensures
        !result@.contains('\t'),
        result@.len() >= s@.len(),
        s@.contains('\t') ==> result@.len() > s@.len(),
        !s@.contains('\t') ==> result@ == s@
{
    let mut result_chars: Vec<char> = Vec::new();
    let mut pos = 0;
    let s_len = s@.len();
    for i in 0..s_len
        invariant
            pos >= 0,
            !result_chars@.contains('\t'),
            result_chars@.len() >= i,
            forall|j: int| 0 <= j < result_chars@.len() ==> result_chars@[j] != '\t'
    {
        let c = s@[i];
        if c == '\t' {
            let spaces_to_add = tab_size - (pos % tab_size);
            for _ in 0..spaces_to_add
                invariant !result_chars@.contains('\t')
            {
                result_chars.push(' ');
            }
            pos += spaces_to_add;
        } else {
            result_chars.push(c);
            pos += 1;
        }
    }
    result_chars.into_iter().collect()
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
    /* code modified by LLM (iteration 5): fix compilation error by using proper ghost operations */
    let mut result: Vec<String> = Vec::new();
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let orig_str: &String = &a[j];
                let result_str: &String = &result[j];
                let tab_sz = tabsize[j];
                (!result_str@.contains('\t')) &&
                (!orig_str@.contains('\t') ==> result_str@ == orig_str@) &&
                (result_str@.len() >= orig_str@.len()) &&
                (orig_str@.contains('\t') ==> result_str@.len() > orig_str@.len())
            }
    {
        let expanded = expand_single_string(&a[i], tabsize[i]);
        result.push(expanded);
    }
    result
}
// </vc-code>

}
fn main() {}