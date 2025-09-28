// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type mismatches by using nat for all weights, indices, and lengths to match Verus sequence operations. */
fn expand_one(s: &String, tabsize: u8) -> (result: String)
    requires
        tabsize > 0,
    ensures
        result@.len() >= s@.len(),
        (forall|c: char| #[trigger] result@.contains(c) ==> c != '\t'),
        (!s@.contains('\t') ==> result@ == s@),
        (s@.contains('\t') ==> result@.len() > s@.len()),
{
    let seq_s = s@;
    let mut result = String::new();
    let mut column: nat = 0;
    let mut j: nat = 0;
    while j < seq_s.len()
        invariant
            column == result@.len(),
            result@.len() >= j,
            forall|k: int| 0 <= k < result@.len() ==> result@[k] == ' ' || (exists|k2: int| 0 <= k2 < j && seq_s[k2] == result@[k]),
            forall|c: char| #[trigger] result@.contains(c) ==> c != '\t',
        decreases seq_s.len() - j
    {
        if seq_s[j] == '\t' {
            let tab: nat = tabsize as nat;
            let rem: nat = column % tab;
            let add: nat = tab - rem;
            let mut k: nat = 0;
            while k < add
                invariant
                    column == result@.len(),
                decreases add - k
            {
                result.push(' ');
                column += 1;
                k += 1;
            }
        } else {
            result.push(seq_s[j]);
            column += 1;
        }
        j += 1;
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
/* code modified by LLM (iteration 5): No changes needed as helper fixes resolve compilation errors, ensuring invariants align with nat types. */
{
    let mut result: Vec<String> = Vec::with_capacity(a.len());
    let mut i = 0;
    while i < a.len()
        invariant
            result@.len() == (i as nat),
            forall|i2: int| 0 <= i2 < result@.len() ==> {
                let orig_str = &a[i2];
                let result_str = &result@[i2];
                let tab_sz = tabsize@[i2];
                result_str@.len() >= orig_str@.len() &&
                (forall|c: char| #[trigger] result_str@.contains(c) ==> c != '\t') &&
                (!orig_str@.contains('\t') ==> result_str@ == orig_str@) &&
                (orig_str@.contains('\t') ==> result_str@.len() > orig_str@.len())
            },
        decreases a.len() - i
    {
        let expanded = expand_one(&a[i], tabsize[i]);
        result.push(expanded);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}