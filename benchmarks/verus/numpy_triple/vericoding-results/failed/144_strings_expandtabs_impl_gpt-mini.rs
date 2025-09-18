// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate that a string contains a tab */
spec fn contains_tab(s: String) -> bool { s@.contains('\t') }
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
    /* code modified by LLM (iteration 5): expand tabs by scanning chars and replacing '\t' with tabsize spaces, avoid String::new by cloning and reusing allocation */
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < a.len() {
        let orig = &a[i];
        let ts = tabsize[i];

        // If there are no tabs, reuse the original string
        if !orig.contains('\t') {
            result.push(orig.clone());
            i += 1;
            continue;
        }

        // Build a new string by reusing a clone's allocation and clearing it
        let mut new_s = orig.clone();
        new_s.clear();

        for ch in orig.chars() {
            if ch == '\t' {
                let mut k: usize = 0;
                while k < ts {
                    new_s.push(' ');
                    k += 1;
                }
            } else {
                new_s.push(ch);
            }
        }

        result.push(new_s);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}