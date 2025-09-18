// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax error by adding missing opening brace */
spec fn get_bit(byte: u8, bit_pos: int) -> u8
    requires 0 <= bit_pos < 8
{
    ((byte as int) / pow(2, (7 - bit_pos) as nat)) % 2
}

fn extract_bits(byte: u8) -> (bits: Vec<u8>)
    ensures bits.len() == 8,
    ensures forall|j: int| 0 <= j < 8 ==> #[trigger] bits[j] == get_bit(byte, j)
{
    let mut bits = Vec::new();
    let mut pos = 0;
    while pos < 8
        invariant 0 <= pos <= 8,
        invariant bits.len() == pos,
        invariant forall|j: int| 0 <= j < pos ==> #[trigger] bits[j] == get_bit(byte, j)
    {
        let bit_val = if (byte & (1u8 << (7 - pos))) != 0 { 1u8 } else { 0u8 };
        proof {
            assert(bit_val == get_bit(byte, pos as int));
        }
        bits.push(bit_val);
        pos += 1;
    }
    bits
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
/* code modified by LLM (iteration 5): kept existing implementation */
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant 0 <= i <= a.len(),
        invariant result.len() == i * 8,
        invariant forall|k: int, j: int| 0 <= k < i && 0 <= j < 8 ==> 
            #[trigger] result[k * 8 + j] == get_bit(a[k], j)
    {
        let byte_bits = extract_bits(a[i]);
        
        let mut j = 0;
        while j < 8
            invariant 0 <= j <= 8,
            invariant result.len() == i * 8 + j,
            invariant forall|k: int, b: int| 0 <= k < i && 0 <= b < 8 ==> 
                #[trigger] result[k * 8 + b] == get_bit(a[k], b),
            invariant forall|b: int| 0 <= b < j ==> 
                #[trigger] result[i * 8 + b] == get_bit(a[i], b)
        {
            result.push(byte_bits[j]);
            j += 1;
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}