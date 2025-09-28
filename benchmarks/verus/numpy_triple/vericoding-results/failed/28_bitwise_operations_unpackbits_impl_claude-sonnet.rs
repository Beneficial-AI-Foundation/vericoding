// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix ghost/exec boundary by using ghost parameter */
fn bit_at_position(byte: u8, pos: usize) -> (result: u8)
    requires
        pos < 8
    ensures
        result == 0 || result == 1,
        result == ((byte as int) / pow(2, (7 - pos as int) as nat)) % 2
{
    let shift_amount = 7 - pos;
    let shifted = byte >> shift_amount;
    shifted & 1
}
// </vc-helpers>

// <vc-spec>
fn numpy_unpackbits(a: Vec<u8>) -> (result: Vec<u8>)
    requires forall|i: int| 0 <= i < a@.len() ==> a@[i] < 256,
    ensures 
        result@.len() == a@.len() * 8,
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < 8 ==> 
            #[trigger] result@[i * 8 + j] == ((a@[i] as int) / pow(2, (7 - j) as nat)) % 2
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use usize for loop variables and casting */
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result@.len() == i * 8,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < 8 ==>
                result@[k * 8 + j] == ((a@[k] as int) / pow(2, (7 - j) as nat)) % 2
    {
        let byte = a[i];
        let mut j = 0;
        
        while j < 8
            invariant
                0 <= j <= 8,
                result@.len() == i * 8 + j,
                forall|k: int, b: int| 0 <= k < i && 0 <= b < 8 ==>
                    result@[k * 8 + b] == ((a@[k] as int) / pow(2, (7 - b) as nat)) % 2,
                forall|b: int| 0 <= b < j ==>
                    result@[i * 8 + b] == ((byte as int) / pow(2, (7 - b) as nat)) % 2
        {
            let bit = bit_at_position(byte, j);
            result.push(bit);
            j += 1;
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}