// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversion - keep usize in exec code */
spec fn char_seq_contains(s: Seq<char>, c: char) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == c
}

fn expand_single_string(s: &String, tab_size: u8) -> (result: String)
    requires
        tab_size > 0,
    ensures
        forall|c: char| #[trigger] result@.contains(c) ==> c != '\t',
        !s@.contains('\t') ==> result@ == s@,
        result@.len() >= s@.len(),
        s@.contains('\t') ==> result@.len() > s@.len(),
{
    let mut result = String::new();
    let mut i: usize = 0;
    let s_len = s.unicode_len();
    
    while i < s_len
        invariant
            i <= s_len,
            s_len == s@.len(),
            forall|j: int| 0 <= j < result@.len() ==> #[trigger] result@[j] != '\t',
            result@.len() >= i as int,
    {
        let c = s.get_char(i);
        if c == '\t' {
            let spaces_to_add = tab_size;
            let mut j: u8 = 0;
            while j < spaces_to_add
                invariant
                    j <= spaces_to_add,
                    forall|k: int| 0 <= k < result@.len() ==> #[trigger] result@[k] != '\t',
            {
                result.push(' ');
                j = j + 1;
            }
        } else {
            result.push(c);
        }
        i = i + 1;
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
    /* code modified by LLM (iteration 5): Main expandtabs implementation */
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == tabsize.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let orig_str = #[trigger] &a[j];
                let result_str = &result[j];
                let tab_sz = tabsize[j] as nat;
                
                (forall|c: char| #[trigger] result_str@.contains(c) ==> c != '\t') &&
                (!orig_str@.contains('\t') ==> result_str@ == orig_str@) &&
                (result_str@.len() >= orig_str@.len()) &&
                (orig_str@.contains('\t') ==> result_str@.len() > orig_str@.len())
            },
    {
        let expanded = expand_single_string(&a[i], tabsize[i]);
        result.push(expanded);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}