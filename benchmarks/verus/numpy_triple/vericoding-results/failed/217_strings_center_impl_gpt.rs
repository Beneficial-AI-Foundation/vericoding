// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): specification capturing per-index correctness of centered output */
spec fn centered_ok_at(a: Vec<String>, width: Vec<usize>, out: Vec<String>, i: int) -> bool {
    let orig_len = a[i]@.len() as int;
    let target_width = width[i] as int;
    &&& (orig_len >= target_width ==> out[i] == a[i])
    &&& out[i]@.len() as int == if orig_len >= target_width { orig_len } else { target_width }
}

// </vc-helpers>

// <vc-spec>
fn center(a: Vec<String>, width: Vec<usize>, fillchar: char) -> (result: Vec<String>)
    requires 
        a.len() == width.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i]@.len() >= 0 && {
                let orig_len = a[i]@.len() as int;
                let target_width = width[i] as int;
                &&& (orig_len >= target_width ==> result[i] == a[i])
                &&& result[i]@.len() as int == if orig_len >= target_width { orig_len } else { target_width }
            }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): avoid unsupported String::new by padding starting from the existing string using push */
    let n = a.len();
    let mut out: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            out.len() == i,
            i <= n,
            n == a.len(),
            width.len() == n,
            forall|k: int| 0 <= k < i ==> centered_ok_at(a, width, out, k),
        decreases (n - i) as int
    {
        let ai = a[i].clone();
        let w = width[i];
        let old_len = out.len();
        if ai.len() >= w {
            out.push(ai.clone());
            proof {
                let k: int = old_len as int;
                assert(k == i as int);
                assert(0 <= k < out.len());
                assert(out[old_len] == ai);
                assert(out[k] == ai);
                assert(ai == a[i]);
                let orig_len: int = a[i]@.len() as int;
                let target_width: int = w as int;
                assert(orig_len >= target_width);
                assert(out[k] == a[i]);
                assert(centered_ok_at(a, width, out, k));
            }
        } else {
            let mut s = ai.clone();
            let mut j: usize = s.len();
            while j < w
                invariant
                    j <= w,
                    s@.len() == j as int,
                decreases (w - j) as int
            {
                s.push(fillchar);
                j = j + 1;
            }
            out.push(s.clone());
            proof {
                let k: int = old_len as int;
                assert(k == i as int);
                assert(0 <= k < out.len());
                assert(out[old_len] == s);
                assert(out[k] == s);
                let orig_len: int = a[i]@.len() as int;
                let target_width: int = w as int;
                assert(orig_len < target_width);
                assert(s@.len() as int == target_width);
                assert(out[k]@.len() as int == target_width);
                assert(centered_ok_at(a, width, out, k));
            }
        }
        i = i + 1;
    }
    out
}
// </vc-code>

}
fn main() {}