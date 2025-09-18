// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper unmodified by LLM (iteration 5) */
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
/* code modified by LLM (iteration 5): Fixed type errors for `int` and `nat` by using `ghost` for conversion variables. */
{
    let mut result: Vec<u8> = Vec::new();
    result.reserve(a.len() * 8);

    for i in 0..a.len() {
        let byte = a[i];
        for j in 0..8 {
            let ghost byte_as_int: int = byte as int;
            let ghost exponent: nat = (7 - j) as nat;
            let ghost bit_val_int: int = (byte_as_int / pow(2, exponent)) % 2;
            let bit_val: u8 = bit_val_int as u8;
            result.push(bit_val);
        }
    }
    result
}
// </vc-code>

}
fn main() {}