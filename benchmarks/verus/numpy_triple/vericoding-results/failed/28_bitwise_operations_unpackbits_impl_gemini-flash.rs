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
/* code modified by LLM (iteration 5): add decreases clause to inner and outer loops */
{
    let mut result: Vec<u8> = Vec::new();
    let vec_len = a.len();
    result.reserve(vec_len * 8);

    let mut i = 0;
    while i < vec_len
        invariant
            0 <= i <= vec_len,
            result@.len() == i * 8,
            forall|k: int, j: int|
                0 <= k < i && 0 <= j < 8 ==> 
                    #[trigger] result@[k * 8 + j] == ((a@[k] as int) / pow(2, (7 - j) as nat)) % 2,
        decreases vec_len - i
    {
        let byte_val = a[i];
        let mut j = 0;
        while j < 8
            invariant
                0 <= j <= 8,
                result@.len() == i * 8 + j,
                forall|k: int, l: int|
                    0 <= k < i && 0 <= l < 8 ==> 
                        #[trigger] result@[k * 8 + l] == ((a@[k] as int) / pow(2, (7 - l) as nat)) % 2,
                forall|l: int|
                    0 <= l < j ==> 
                        #[trigger] result@[i * 8 + l] == (((byte_val as int) / pow(2, (7 - l) as nat)) % 2),
            decreases 8 - j
        {
            let bit_val: u8 = (byte_val >> (7 - j)) & 1;
            result.push(bit_val);
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}