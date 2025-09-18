// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): computes bit j of a byte */
spec fn byte_bit(a: u8, j: nat) -> int
    requires j < 8
{
    ((a as int) / pow(2, (7 - j) as nat)) % 2
}

/* helper modified by LLM (iteration 5): proof that byte_bit is 0 or 1 */
proof fn byte_bit_bounds(a: u8, j: nat)
    requires j < 8
    ensures 0 <= byte_bit(a, j) && byte_bit(a, j) <= 1
{
    assert(0 <= ((a as int) / pow(2, (7 - j) as nat)) % 2);
    assert(((a as int) / pow(2, (7 - j) as nat)) % 2 <= 1);
}
// </vc-helpers>

// <vc-spec>
fn numpy_unpackbits(a: Vec<u8>) -> (result: Vec<u8>)
    requires forall|i: int| 0 <= i < a.len() ==> a[i] < 256,
    ensures 
        result.len() == a.len() * 8,
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < 8 ==> 
            #[trigger] result[i * 8 + j] == ((a[i] as int) / pow(2, (7 - j) as nat)) % 2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): unpack bytes into bits using byte_bit helper */
    let mut result: Vec<u8> = Vec::new();
    let mut i: int = 0;
    while i < a.len()
        invariant 0 <= i && i <= a.len(),
        invariant result.len() == i * 8,
        invariant forall|p: int, q: int| 0 <= p && p < i && 0 <= q && q < 8 ==> result[p * 8 + q] as int == byte_bit(a[p], q as nat),
        decreases a.len() - i
    {
        let mut j: int = 0;
        while j < 8
            invariant 0 <= j && j <= 8,
            invariant result.len() == i * 8 + j,
            invariant forall|p: int, q: int| 0 <= p && p < i && 0 <= q && q < 8 ==> result[p * 8 + q] as int == byte_bit(a[p], q as nat),
            invariant forall|q: int| 0 <= q && q < j ==> result[i * 8 + q] as int == byte_bit(a[i], q as nat),
            decreases 8 - j
        {
            let b_int: int = byte_bit(a[i], j as nat);
            result.push(b_int as u8);
            j += 1;
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}