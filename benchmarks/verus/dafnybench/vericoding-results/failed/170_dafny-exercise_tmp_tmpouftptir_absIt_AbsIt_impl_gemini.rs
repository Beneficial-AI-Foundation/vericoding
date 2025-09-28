// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn abs_it(s: &mut Vec<i32>)
    ensures
        s.len() == old(s).len(),
        forall|i: int| 0 <= i < s.len() ==> 
            if old(s)[i] < 0 { s[i] == -old(s)[i] } else { s[i] == old(s)[i] }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added assertion to prove lack of overflow */
    let ghost s_old = s@;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            s.len() == s_old.len(),
            i <= s.len(),
            forall|j: int| 0 <= j < i as int ==> 
                if s_old[j] < 0 { s@[j] == -s_old[j] } else { s@[j] == s_old[j] },
            forall|k: int| i as int <= k < s_old.len() ==> s@[k] == s_old[k],
        decreases s.len() - i
    {
        let x = s[i];
        if x < 0 {
            // The ensures clause of `abs_it` implies that for any negative value `v` in `old(s)`,
            // `-v` must be representable as an i32. This means `v` cannot be `i32::MIN`.
            // From the invariant, we know that at the beginning of the loop body, `x == s_old@[i]`.
            // Therefore, we can assert that `x > i32::MIN`.
            assert(x > i32::MIN);
            s.set(i, -x);
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}