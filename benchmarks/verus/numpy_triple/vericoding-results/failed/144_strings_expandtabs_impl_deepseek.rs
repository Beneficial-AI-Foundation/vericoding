// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix spec function parameter name from result to expanded */
proof fn lemma_seq_len_after_tab_expansion(orig: Seq<char>, tab_sz: nat) -> (expanded_len: nat)
    requires
        tab_sz > 0,
    ensures
        expanded_len >= orig.len(),
        orig.contains('\t') ==> expanded_len > orig.len()
{
    if orig.len() == 0 {
        0
    } else {
        let rest_len = lemma_seq_len_after_tab_expansion(orig.drop_last(), tab_sz);
        if orig.last() == '\t' {
            rest_len + tab_sz
        } else {
            rest_len + 1
        }
    }
}

spec fn expand_tab_char(ch: char, tab_sz: nat) -> Seq<char>
    requires
        tab_sz > 0,
    ensures
        ch == '\t' ==> result.len() == tab_sz,
        ch != '\t' ==> result.len() == 1 && result[0] == ch
{
    if ch == '\t' {
        Seq::new(tab_sz, |i: int| ' ')
    } else {
        seq![ch]
    }
}

proof fn lemma_concat_expanded_chars(s: Seq<char>, tab_sz: nat) -> (expanded: Seq<char>)
    requires
        tab_sz > 0,
    ensures
        expanded.len() >= s.len(),
        s.contains('\t') ==> expanded.len() > s.len(),
        forall|c: char| expanded.contains(c) ==> c != '\t'
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        let head_expanded = expand_tab_char(s[0], tab_sz);
        let tail_expanded = lemma_concat_expanded_chars(s.drop_first(), tab_sz);
        head_expanded + tail_expanded
    }
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
/* code modified by LLM (iteration 5): Fix compilation error - change spec result to expanded */
{
    let mut output: Vec<String> = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            output.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let orig_str = &a[j];
                let result_str = &output[j];
                let tab_sz = tabsize[j];
                
                (forall|c: char| result_str@.contains(c) ==> c != '\t') &&
                (!orig_str@.contains('\t') ==> result_str@ == orig_str@) &&
                (result_str@.len() >= orig_str@.len()) &&
                (orig_str@.contains('\t') ==> result_str@.len() > orig_str@.len())
            }
    {
        let orig_str = &a[i];
        let tab_size = tabsize[i];
        let mut expanded_chars: Vec<char> = Vec::new();
        let mut j: usize = 0;
        
        while j < orig_str.len()
            invariant
                0 <= j <= orig_str.len(),
                forall|c: char| expanded_chars@.contains(c) ==> c != '\t',
                expanded_chars@.len() >= j,
                orig_str@.contains('\t') ==> expanded_chars@.len() > j || j < orig_str.len()
        {
            let c = orig_str.as_bytes()[j] as char;
            if c == '\t' {
                let mut k: usize = 0;
                while k < tab_size
                    invariant
                        0 <= k <= tab_size,
                        expanded_chars@.len() == old(expanded_chars)@.len() + k,
                        forall|c: char| expanded_chars@.contains(c) ==> c != '\t' || c == ' '
                {
                    expanded_chars.push(' ');
                    k += 1;
                }
            } else {
                expanded_chars.push(c);
            }
            j += 1;
        }
        
        let expanded_string = String::from_chars(expanded_chars);
        output.push(expanded_string);
        i += 1;
    }
    output
}
// </vc-code>

}
fn main() {}