// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn expand_single_string(s: Seq<char>, tab_sz: nat) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let c = s[0];
        let rest = s.skip(1);
        if c == '\t' {
            let spaces = seq![' '; tab_sz as nat];
            spaces + expand_single_string(rest, tab_sz)
        } else {
            seq![c] + expand_single_string(rest, tab_sz)
        }
    }
}

proof fn expand_single_string_no_tabs(s: Seq<char>, tab_sz: nat)
    requires 
        tab_sz > 0,
        forall|i: int| 0 <= i < s.len() ==> s[i] != '\t'
    ensures
        expand_single_string(s, tab_sz) == s
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        expand_single_string_no_tabs(s.skip(1), tab_sz);
    }
}

proof fn expand_single_string_has_no_tabs(s: Seq<char>, tab_sz: nat)
    requires tab_sz > 0
    ensures forall|c: char| expand_single_string(s, tab_sz).contains(c) ==> c != '\t'
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        expand_single_string_has_no_tabs(s.skip(1), tab_sz);
    }
}

proof fn expand_single_string_length(s: Seq<char>, tab_sz: nat)
    requires tab_sz > 0
    ensures 
        expand_single_string(s, tab_sz).len() >= s.len(),
        s.contains('\t') ==> expand_single_string(s, tab_sz).len() > s.len()
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let c = s[0];
        let rest = s.skip(1);
        expand_single_string_length(rest, tab_sz);
        if c == '\t' {
            assert(expand_single_string(s, tab_sz).len() == tab_sz + expand_single_string(rest, tab_sz).len());
            assert(tab_sz > 0);
            assert(expand_single_string(rest, tab_sz).len() >= rest.len());
            assert(expand_single_string(s, tab_sz).len() > s.len());
        }
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
{
    /* code modified by LLM (iteration 5): use from_vec instead of non-existent new_from_vec */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let orig_str = &a[j];
                let result_str: &String = &result[j];
                let tab_sz = tabsize[j];
                (forall|c: char| result_str@.contains(c) ==> c != '\t') &&
                (!orig_str@.contains('\t') ==> result_str@ == orig_str@) &&
                (result_str@.len() >= orig_str@.len()) &&
                (orig_str@.contains('\t') ==> result_str@.len() > orig_str@.len())
            }
    {
        let orig_str = &a[i];
        let tab_sz = tabsize[i];
        let ghost tab_sz_nat = tab_sz as nat;
        let ghost expanded = expand_single_string(orig_str@, tab_sz_nat);
        
        proof {
            expand_single_string_has_no_tabs(orig_str@, tab_sz_nat);
            expand_single_string_length(orig_str@, tab_sz_nat);
            if !orig_str@.contains('\t') {
                expand_single_string_no_tabs(orig_str@, tab_sz_nat);
            }
        }
        
        let mut new_chars = Vec::new();
        let mut j = 0;
        while j < orig_str.len()
            invariant
                j <= orig_str.len(),
                new_chars@.len() >= j,
                forall|c: char| new_chars@.contains(c) ==> c != '\t'
        {
            let c = orig_str.get_char(j);
            if c == '\t' {
                let mut k = 0;
                while k < tab_sz
                    invariant
                        k <= tab_sz,
                        forall|c: char| new_chars@.contains(c) ==> c != '\t'
                {
                    new_chars.push(' ');
                    k = k + 1;
                }
            } else {
                new_chars.push(c);
            }
            j = j + 1;
        }
        
        let new_str = String::from_vec(new_chars);
        result.push(new_str);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}