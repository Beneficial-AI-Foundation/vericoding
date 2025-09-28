// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    let mut result: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result@.len() == i * 8,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < 8 ==> 
                #[trigger] result@[k * 8 + j] == ((a@[k] as int) / pow(2, (7 - j) as nat)) % 2,
            forall|k: int| 0 <= k < a@.len() ==> a@[k] < 256,
    {
        let byte = a[i];
        let mut j: usize = 0;
        
        while j < 8
            invariant
                j <= 8,
                i < a.len(),
                result@.len() == i * 8 + j,
                forall|k: int, m: int| 0 <= k < i && 0 <= m < 8 ==> 
                    #[trigger] result@[k * 8 + m] == ((a@[k] as int) / pow(2, (7 - m) as nat)) % 2,
                forall|m: int| 0 <= m < j ==> 
                    result@[i * 8 + m] == ((byte as int) / pow(2, (7 - m) as nat)) % 2,
                byte == a@[i],
                byte < 256,
                forall|k: int| 0 <= k < a@.len() ==> a@[k] < 256,
        {
            let shift_amount: u32 = (7 - j) as u32;
            let bit_value = (byte >> shift_amount) & 1;
            
            proof {
                assert(bit_value == ((byte as int) / pow(2, shift_amount as nat)) % 2) by (bit_vector);
            }
            
            result.push(bit_value);
            j = j + 1;
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}