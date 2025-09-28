// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): byte-match predicate as spec helper */
spec fn matches_byte(s_b: u8, p_b: u8) -> bool {
    s_b == p_b || p_b == '?' as u8
}
// </vc-helpers>

// <vc-spec>
fn match_strings(s: &str, p: &str) -> (result: bool)
    requires s@.len() == p@.len(),
    ensures
        result == (forall|n: int| 0 <= n < s@.len() ==> 
            (s@.index(n) == p@.index(n) || p@.index(n) == '?' as u8)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): avoid str::len() by using as_bytes().len() and maintain invariants over indices */
    let s_bytes = s.as_bytes();
    let p_bytes = p.as_bytes();
    let n: usize = s_bytes.len();
    let mut i: usize = 0;
    while i < n
        invariant
            s@.len() == p@.len(),
            n as int == s@.len(),
            0 <= i as int <= n as int,
            forall|k: int| 0 <= k < i as int ==> (s@.index(k) == p@.index(k) || p@.index(k) == '?' as u8),
        decreases (n - i) as int
    {
        let sb = s_bytes[i];
        let pb = p_bytes[i];
        if !(sb == pb || pb == '?' as u8) {
            proof {
                let gi = i as int;
                assert(0 <= gi && gi < s@.len());
                assert(s@.index(gi) == sb);
                assert(p@.index(gi) == pb);
                assert(!(s@.index(gi) == p@.index(gi) || p@.index(gi) == '?' as u8));
            }
            return false;
        }
        i += 1;
    }
    proof {
        let li = i as int;
        assert(li == n as int);
        assert(n as int == s@.len());
        assert(forall|k: int| 0 <= k < s@.len() ==> (s@.index(k) == p@.index(k) || p@.index(k) == '?' as u8));
    }
    true
}
// </vc-code>

}
fn main() {}