// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): target length computation */
spec fn target_len(orig_len: int, width: int) -> int { if orig_len >= width { orig_len } else { width } }

/* helper modified by LLM (iteration 4): simple max function for ints (spec) */
spec fn max_int(a: int, b: int) -> int { if a >= b { a } else { b } }

/* helper modified by LLM (iteration 4): bounds lemma for target_len */
proof fn target_len_bounds(orig_len: int, width: int)
    ensures target_len(orig_len, width) >= orig_len,
            target_len(orig_len, width) >= width
{
    if orig_len >= width {
        assert(target_len(orig_len, width) == orig_len);
        assert(target_len(orig_len, width) >= width);
    } else {
        assert(target_len(orig_len, width) == width);
        assert(target_len(orig_len, width) >= orig_len);
    }
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
    /* code modified by LLM (iteration 4): fix type mismatch in proof (compare String views) and implement padding */
    let n = a.len();
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            width.len() == n,
            result.len() == i,
            0 <= i as int <= n as int,
            forall|j: int| 0 <= j < i as int ==> {
                let orig_len = a@[j]@.len() as int;
                let target_width = width@[j] as int;
                &&& (orig_len >= target_width ==> result@[j] == a@[j])
                &&& result@[j]@.len() as int == if orig_len >= target_width { orig_len } else { target_width }
            }
        decreases n as int - i as int
    {
        let mut s = a[i].clone();
        let ghost ii: int = i as int;
        let tw: usize = width[i];
        let orig_k: usize = s.len();
        proof {
            assert(0 <= ii && ii < n as int);
            assert(width@[ii] == tw);
            assert(a@[ii]@.len() as int == orig_k as int);
        }
        if orig_k < tw {
            let mut k: usize = orig_k;
            while k != tw
                invariant
                    s@.len() == k as int,
                    k as int <= tw as int,
                    k as int >= a@[ii]@.len() as int,
                    width@[ii] == tw,
                    0 <= ii && ii < n as int
                decreases tw as int - k as int
            {
                s.push(fillchar);
                k = k + 1;
            }
            proof {
                assert(s@.len() == tw as int);
            }
        } else {
            proof {
                assert(s@ == a@[ii]@);
            }
        }
        proof {
            let orig_len_i = a@[ii]@.len() as int;
            let target_width_i = width@[ii] as int;
            if orig_len_i >= target_width_i {
                assert(s@ == a@[ii]@);
                assert(s@.len() as int == orig_len_i);
            } else {
                assert(s@.len() as int == target_width_i);
            }
        }
        result.push(s);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}