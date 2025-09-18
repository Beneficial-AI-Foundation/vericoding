// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed compilation errors by casting sequence len to int and using proper indexing */
    let mut result: Vec<String> = Vec::new();
    for i in 0..a.len() {
        let tab_sz = tabsize[i];
        let mut new_chars: Vec<char> = Vec::new();
        let mut col: usize = 0;
        let orig = a@[i];
        let len = orig.len() as int;
        for j in 0..len {
            let c = orig[j];
            if c == '\t' {
                let spaces = if col % tab_sz == 0 { tab_sz } else { tab_sz - (col % tab_sz) };
                for _ in 0..spaces {
                    new_chars.push(' ');
                    col += 1;
                }
            } else {
                new_chars.push(c);
                col += 1;
            }
        }
        let new_str: String = new_chars.into_iter().collect();
        result.push(new_str);
    }
    result
}
// </vc-code>

}
fn main() {}