// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): updated lemma calls to functions in vstd::arithmetic::div_mod */
proof fn get_bit_lemma(val: u8, j: nat)
    requires j < 8,
    ensures (val >> j) & 1 == (val as int / pow(2, j)) % 2,
{
    vstd::arithmetic::div_mod::lemma_div_by_pow2_is_shr(val as int, j);
    vstd::arithmetic::div_mod::lemma_mod_by_2_is_bit_and_1(val as int >> j);
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
/* code modified by LLM (iteration 5): No changes needed, logic depends on fixed helper */
{
    let mut result: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i * 8,
            forall|k: int, j: int| 0 <= k < (i as int) && 0 <= j < 8 ==>
                #[trigger] result@[(k * 8 + j) as nat] == ((a@[k] as int) / pow(2, (7 - j) as nat)) % 2,
    {
        let val = a[i];
        let mut j: usize = 0;
        while j < 8
            invariant
                0 <= j <= 8,
                i < a.len(),
                val == a@[i as int],
                result.len() == i * 8 + j,
                forall|k: int, l: int| 0 <= k < (i as int) && 0 <= l < 8 ==>
                    #[trigger] result@[(k * 8 + l) as nat] == ((a@[k] as int) / pow(2, (7 - l) as nat)) % 2,
                forall|l: int| 0 <= l < (j as int) ==>
                    #[trigger] result@[((i as int) * 8 + l) as nat] == ((val as int) / pow(2, (7 - l) as nat)) % 2,
        {
            let bit_val = (val >> (7 - j)) & 1;

            proof {
                get_bit_lemma(val, (7 - j) as nat);
            }
            
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