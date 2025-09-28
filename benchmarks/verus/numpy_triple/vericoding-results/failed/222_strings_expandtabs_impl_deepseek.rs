// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix Chars iterator length checking and invariants */
fn process_string(s: &String, tabsize: u8) -> (res: String)
    requires
        tabsize > 0,
    ensures
        forall|c: char| #[trigger] res@.contains(c) ==> c != '\t',
        !s@.contains('\t') ==> res@ == s@,
        res@.len() >= s@.len(),
        s@.contains('\t') ==> res@.len() > s@.len(),
{
    let mut result = String::new();
    let mut pos: usize = 0;
    let mut chars_iter = s.chars();
    
    while true
        invariant
            pos >= 0,
            forall|ch: char| #[trigger] result@.contains(ch) ==> ch != '\t',
            result@.len() >= pos,
    {
        let next_char = chars_iter.next();
        if next_char.is_none() {
            break;
        }
        let c = next_char.unwrap();
        if c == '\t' {
            let spaces_needed = tabsize as usize - (pos % tabsize as usize);
            let spaces = " ".repeat(spaces_needed);
            result.push_str(&spaces);
            pos += spaces_needed;
        } else {
            result.push(c);
            if c == '\n' || c == '\r' {
                pos = 0;
            } else {
                pos += 1;
            }
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
    /* code modified by LLM (iteration 5): Maintain implementation with correct helper usage */
    let mut result_vec: Vec<String> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let orig_str = &a[j];
                let result_str: &String = &result_vec[j];
                let tab_sz = tabsize[j] as nat;
                
                (forall|c: char| #[trigger] result_str@.contains(c) ==> c != '\t') &&
                (!orig_str@.contains('\t') ==> result_str@ == orig_str@) &&
                (result_str@.len() >= orig_str@.len()) &&
                (orig_str@.contains('\t') ==> result_str@.len() > orig_str@.len())
            },
    {
        let processed = process_string(&a[i], tabsize[i]);
        result_vec.push(processed);
        i += 1;
    }
    
    result_vec
}
// </vc-code>

}
fn main() {}