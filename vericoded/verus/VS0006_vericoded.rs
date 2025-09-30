// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): spec function to express bitwise-or in u32 */
pub open spec fn or_u8_u32(a: u8, b: u8) -> u32 {
    (a as u32) | (b as u32)
}

// </vc-helpers>

// <vc-spec>
fn bitwise_or(a: Vec<u8>, b: Vec<u8>) -> (result: Vec<u8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as u32 == (a[i] as u32 | b[i] as u32),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): use seq view (@) in assertions/invariants and relate exec indexing to spec */
    let n = a.len();
    let mut res: Vec<u8> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            a.len() == n,
            b.len() == n,
            i <= n,
            res.len() == i,
            forall|j: int|
                0 <= j < i as int ==> res@[j] as u32 == ((a@[j] as u32) | (b@[j] as u32)),
        decreases (n as int) - (i as int)
    {
        let ai = a[i];
        let bi = b[i];
        let c: u8 = ai | bi;
        res.push(c);
        assert(i < res.len());
        let ri = res[i];
        proof {
            assert(ri == res@[i as int]);
            assert(ai == a@[i as int]);
            assert(bi == b@[i as int]);
        }
        assert(res@[i as int] as u32 == ((a@[i as int] as u32) | (b@[i as int] as u32)));
        i = i + 1;
    }

    res
}

// </vc-code>


}
fn main() {}