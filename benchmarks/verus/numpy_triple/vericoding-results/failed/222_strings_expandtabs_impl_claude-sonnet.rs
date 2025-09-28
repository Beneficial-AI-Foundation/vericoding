// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): replaced byte literal with u8 value */
fn expand_single_string(s: &String, tab_size: u8) -> (result: String)
    requires
        tab_size > 0,
    ensures
        !result@.contains('\t'),
        result@.len() >= s@.len(),
        !s@.contains('\t') ==> result@ == s@,
        s@.contains('\t') ==> result@.len() > s@.len(),
{
    let mut result = String::new();
    let mut pos = 0;
    
    for i in 0..s.len()
        invariant
            !result@.contains('\t'),
            result@.len() >= i,
            pos >= i,
            !s@.subrange(0, i as int).contains('\t') ==> result@ == s@.subrange(0, i as int),
            s@.subrange(0, i as int).contains('\t') ==> result@.len() > i,
    {
        let byte_val = s.as_bytes()[i];
        if byte_val == 9u8 {
            let spaces_needed = tab_size as usize - (pos % tab_size as usize);
            for _ in 0..spaces_needed
                invariant
                    !result@.contains('\t'),
            {
                result.push(' ');
                pos += 1;
            }
        } else {
            let c = byte_val as char;
            result.push(c);
            pos += 1;
        }
    }
    result
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
    /* code modified by LLM (iteration 5): no changes to main function body */
    let mut result = Vec::new();
    
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let orig_str = &a[j];
                let result_str: &String = &result[j];
                let tab_sz = tabsize[j] as nat;
                
                (!result_str@.contains('\t')) &&
                (!orig_str@.contains('\t') ==> result_str@ == orig_str@) &&
                (result_str@.len() >= orig_str@.len()) &&
                (orig_str@.contains('\t') ==> result_str@.len() > orig_str@.len())
            },
    {
        let expanded = expand_single_string(&a[i], tabsize[i]);
        result.push(expanded);
    }
    
    result
}
// </vc-code>

}
fn main() {}