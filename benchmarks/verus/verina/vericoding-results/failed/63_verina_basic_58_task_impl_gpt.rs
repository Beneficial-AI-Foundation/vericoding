// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): executable helper to double an i32 with a spec link to int */
fn dbl_i32(x: i32) -> (y: i32)
    ensures
        y as int == 2 * x
{
    x + x
}

// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == 2 * s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): use executable helper to avoid int/i32 mismatch in proofs */
    let n = s.len();
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == s.len(),
            i <= n,
            out@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] out@[j] == 2 * s@[j],
        decreases n - i
    {
        let x = s[i];
        let ghost pre = out@;
        let y = dbl_i32(x);
        out.push(y);
        proof {
            assert(i < n);
            assert(n == s.len());
            assert(i < s.len());
            assert(x == s@[i as int]);
            assert(pre.len() == i as int);
            assert(out@ == pre.push(y));
            assert(y as int == 2 * x);
            assert(out@[i as int] == y);
            assert(out@[i as int] == 2 * s@[i as int]);
        }
        i += 1;
    }
    out
}
// </vc-code>

}
fn main() {}