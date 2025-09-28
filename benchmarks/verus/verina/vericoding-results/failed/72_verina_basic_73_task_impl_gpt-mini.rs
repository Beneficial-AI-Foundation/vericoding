// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): compare byte at index with pattern (supports '?') */
fn substr_byte_match(s: &str, p: &str, i: usize) -> bool {
    let sb = s.as_bytes();
    let pb = p.as_bytes();
    if i < sb.len() && i < pb.len() {
        let sp = sb[i];
        let pp = pb[i];
        sp == pp || pp == b'?'
    } else {
        false
    }
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
    /* code modified by LLM (iteration 3): iterate bytes and maintain invariant linking ok to spec */
    let mut i: usize = 0;
    let mut ok: bool = true;
    while i < s.len()
        invariant
            0 <= i && i <= s.len(),
            ok == (forall|k: int| 0 <= k < i as int ==> (s@.index(k) == p@.index(k) || p@.index(k) == '?' as u8)),
        decreases s.len() - i
    {
        let sb = s.as_bytes();
        let pb = p.as_bytes();
        if sb[i] != pb[i] && pb[i] != b'?' {
            ok = false;
        }
        i = i + 1;
    }
    ok
}
// </vc-code>

}
fn main() {}