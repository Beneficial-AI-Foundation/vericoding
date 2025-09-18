// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): spec predicate to check if a sequence contains a tab */
pub open spec fn contains_tab(s: Seq<char>) -> bool {
    s.contains('\t')
}

/* helper modified by LLM (iteration 4): predicate stating a sequence has no tab characters */
pub open spec fn no_tabs(s: Seq<char>) -> bool {
    forall|c: char| s.contains(c) ==> c != '\t'
}

/* helper modified by LLM (iteration 4): compute the length of the string after expanding tabs into (tab_sz + 1) spaces */
pub open spec fn expanded_len(s: Seq<char>, tab_sz: nat) -> nat
    decreases s.len()
{
    if s.len() == 0 { 0 } else {
        let head = s[0];
        let tail = s.subrange(1, s.len() as int);
        if head == '\t' { (tab_sz + 1) + expanded_len(tail, tab_sz) } else { 1 + expanded_len(tail, tab_sz) }
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
    /* code modified by LLM (iteration 4): expand tabs by replacing each '\t' with (tabsize[i] + 1) spaces; preserve original when no tabs */
    let n = a.len();
    let mut out_vec: Vec<String> = Vec::new();
    out_vec.reserve(n);

    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            out_vec.len() == i,
            n == a.len(),
            a.len() == tabsize.len()
    {
        let s = &a[i];
        let tsz = tabsize[i];
        let mut out = String::new();
        let mut saw_tab = false;

        // Build the output by scanning characters; replace tabs with (tsz + 1) spaces
        for ch in s.chars() {
            if ch == '\t' {
                saw_tab = true;
                let target: usize = tsz + 1;
                let mut k: usize = 0;
                while k < target
                    invariant
                        k <= target,
                        out@.len() >= 0
                {
                    out.push(' ');
                    k += 1;
                }
            } else {
                out.push(ch);
            }
        }

        // If no tab was seen, then out is identical to s because we pushed each original char unchanged
        // Otherwise, out contains only non-tab characters and is strictly longer than s
        if !saw_tab {
            // Replace with original to make equality explicit in this branch
            out = s.clone();
        } else {
            proof {
                // out contains only characters that are either original non-tab chars or spaces
                assert(forall|c: char| out@.contains(c) ==> c != '\t');
            }
        }

        out_vec.push(out);
        i += 1;
    }

    out_vec
}
// </vc-code>

}
fn main() {}