// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for prefix matching up to i */
spec fn prefix_matches(s: Seq<u8>, p: Seq<u8>, i: int) -> bool {
    forall|n: int| 0 <= n < i ==> (s.index(n) == p.index(n) || p.index(n) == '?' as u8)
}

/* helper modified by LLM (iteration 5): relate runtime string length and spec sequence length */
proof fn str_len_eq_seq_len(s: &str) ensures s.len() as int == s@.len() {
    proof {
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
    /* code modified by LLM (iteration 5): runtime loop comparing bytes and proving equivalence with spec */
    let len_usize = s.len();
    let len = len_usize as int;
    let sb = s.as_bytes();
    let pb = p.as_bytes();
    let mut i = 0usize;
    let mut ok: bool = true;
    while i < len_usize
        invariant 0 <= i as int <= len
        invariant ok == prefix_matches(s@, p@, i as int)
        decreases len_usize - i
    {
        if !(sb[i] == pb[i] || pb[i] == b'?') {
            ok = false;
            i = len_usize;
        } else {
            i += 1;
        }
    }
    proof {
        assert(s.len() as int == s@.len());
        assert(len == s@.len());
        assert(ok == prefix_matches(s@, p@, len));
    }
    ok
}
// </vc-code>

}
fn main() {}