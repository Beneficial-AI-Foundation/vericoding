// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed requires/ensures from spec functions to fix compilation error */
spec fn get_bit(byte: int, j: nat) -> int
{
    (byte / pow(2, (7 - j) as nat)) % 2
}

spec fn bit_shift(byte: int, j: nat) -> int
{
    byte / pow(2, (7 - j) as nat)
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
/* code modified by LLM (iteration 5): Fixed compilation error in spec functions */
{
    let mut result: Vec<u8> = Vec::with_capacity((a.len() * 8) as usize);
    let a_len = a.len();
    for i in 0..a_len
        invariant result.len() == i * 8,
                 forall |k: int| 0 <= k < i ==> 
                     (forall |pos: nat| pos < 8 ==> result@[k * 8 + pos as int] == ((((a@[k] as int) / pow(2, (7 - pos) as nat)) % 2) as u8)),
                 a_len == a.len(),
                 forall |x: int| 0 <= x < a_len ==> a@[x] < 256
    {
        let byte_val = a[i];
        for j in 0..8
            invariant result.len() == i * 8 + j,
                     forall |k: int| 0 <= k < i ==> 
                         (forall |pos: nat| pos < 8 ==> result@[k * 8 + pos as int] == ((((a@[k] as int) / pow(2, (7 - pos) as nat)) % 2) as u8)),
                     forall |pos: nat| pos < j ==> result@[i * 8 + pos as int] == ((((byte_val as int) / pow(2, (7 - pos) as nat)) % 2) as u8),
                     a_len == a.len(),
                     forall |x: int| 0 <= x < a_len ==> a@[x] < 256
        {
            let value = (byte_val as u32) >> (7u32 - j as u32);
            let bit = (value & 1) as u8;
            result.push(bit);
        }
    }
    assert(result.len() == a_len * 8);
    assert(forall |i_pi: int, j_pi: int| 0 <= i_pi < a_len && 0 <= j_pi < 8 ==> 
             #[trigger] result@[i_pi * 8 + j_pi] == ((((a@[i_pi] as int) / pow(2, (7 - j_pi) as nat)) % 2) as u8));
    result
}
// </vc-code>

}
fn main() {}