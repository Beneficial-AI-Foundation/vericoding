// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute number of spaces to next tab stop */
fn spaces_for(col: usize, tab: usize) -> usize
    requires
        tab > 0,
    ensures
        result >= 1,
        result <= tab,
        (col + result) % tab == 0,
{
    let rem = col % tab;
    if rem == 0 {
        tab
    } else {
        tab - rem
    }
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
    /* code modified by LLM (iteration 5): implement expandtabs using usize loop conditions and runtime char access */
    let mut res: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> {
                let orig = &a[j as usize];
                let resj = &res[j as usize];
                let tab_sz = tabsize[j as usize] as nat;

                (forall|c: char| #[trigger] resj@.contains(c) ==> c != '\t') &&

                (!orig@.contains('\t') ==> resj@ == orig@) &&

                (resj@.len() >= orig@.len()) &&

                (orig@.contains('\t') ==> resj@.len() > orig@.len())
            },
        decreases a.len() - i
    {
        let s = &a[i];
        let ts: usize = tabsize[i] as usize;
        let mut out: String = String::new();
        let mut col: usize = 0;
        let mut k: usize = 0;
        while k < s.len()
            invariant
                k <= s.len(),
                (col as int) == out@.len(),
            decreases s.len() - k
        {
            let ch_opt = s.chars().nth(k);
            match ch_opt {
                Some(ch) => {
                    if ch != '\t' {
                        out.push_char(ch);
                        col = col + 1;
                    } else {
                        let sp = spaces_for(col, ts);
                        let old_col = col;
                        let mut t: usize = 0;
                        while t < sp
                            invariant
                                t <= sp,
                                out@.len() == old_col as int + t as int,
                            decreases sp - t
                        {
                            out.push_char(' ');
                            t = t + 1;
                        }
                        col = old_col + sp;
                    }
                }
                None => {
                    // should not happen because k < s.len()
                }
            }
            k = k + 1;
        }
        proof {
            let mut idx2: nat = 0;
            while idx2 < out@.len()
                invariant 0 <= idx2 <= out@.len(),
                decreases out@.len() - idx2
            {
                assert(out@[idx2] != '\t');
                idx2 = idx2 + 1;
            }
            if (!s@.contains('\t')) {
                assert(out@.len() == s@.len());
                let mut j: nat = 0;
                while j < out@.len()
                    invariant 0 <= j <= out@.len(),
                    decreases out@.len() - j
                {
                    assert(out@[j] == s@[j]);
                    j = j + 1;
                }
            } else {
                assert(out@.len() > s@.len());
            }
        }
        res.push(out);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}