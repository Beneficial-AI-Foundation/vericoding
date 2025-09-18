// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove unused helper and fix pow function reference */
spec fn bit_at(byte: u8, pos: nat) -> int
    requires pos < 8,
    ensures
        result == ((byte as int) / pow(2, (7 - pos) as nat)) % 2
{
    ((byte as int) / pow(2, (7 - pos) as nat)) % 2
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
/* code modified by LLM (iteration 5): Fix result calculation and use bit shifting approach */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i * 8,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < 8 ==> 
                #[trigger] result[k * 8 + j] == ((a[k] as int) / pow(2, (7 - j) as nat)) % 2
    {
        let byte = a[i];
        let mut j: usize = 0;
        while j < 8
            invariant
                0 <= j <= 8,
                result.len() == i * 8 + j,
                forall|p: int| 0 <= p < j ==> 
                    #[trigger] result[i * 8 + p] == ((byte as int) / pow(2, (7 - p) as nat)) % 2
        {
            let bit = ((byte >> (7 - j)) & 1) as u8;
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