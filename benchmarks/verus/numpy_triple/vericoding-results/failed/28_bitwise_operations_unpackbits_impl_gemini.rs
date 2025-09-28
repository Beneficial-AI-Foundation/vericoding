// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [Fixed compilation error by correcting path for bitwise lemmas] */
fn unpack_byte(byte: u8) -> (result: Seq<u8>)
    ensures
        result.len() == 8,
        forall|j: int| 0 <= j < 8 ==> 
            #[trigger] result[j] == ((byte as int) / pow(2, (7 - j) as nat)) % 2,
{
    let mut bits = Seq::<u8>::empty();
    let mut j: usize = 0;
    while j < 8
        invariant
            0 <= j <= 8,
            bits.len() == j,
            forall|k: int| 0 <= k < j ==> 
                #[trigger] bits[k] == ((byte as int) / pow(2, (7 - k) as nat)) % 2,
        decreases 8 - j,
    {
        let k_usize: usize = 7 - j;
        let bit = (byte >> k_usize) & 1;
        proof {
            let k_nat = k_usize as nat;
            vstd::lemmas::shr_is_div_pow2(byte as nat, k_nat);
            let val = (byte as nat) >> k_nat;
            vstd::lemmas::bit_and_is_mod_pow2(val, 1);
            assert(bit as int == ((byte as int) / pow(2, (7 - j) as nat)) % 2);
        }
        bits = bits.push(bit);
        j = j + 1;
    }
    bits
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
/* code modified by LLM (iteration 5): [No changes; fixing compilation error in helper function.] */
{
    let mut result = Vec::<u8>::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a@ == old(a)@,
            result@.len() == i * 8,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < 8 ==> 
                #[trigger] result@[(k * 8 + j)] == ((a@[k] as int) / pow(2, (7 - j) as nat)) % 2,
        decreases a.len() - i
    {
        let byte = a[i];
        let bits_seq = unpack_byte(byte);

        let mut j: usize = 0;
        while j < 8
            invariant
                0 <= j <= 8,
                i < a.len(),
                a@ == old(a)@,
                bits_seq == unpack_byte(a@[i]),
                result@.len() == i * 8 + j,
                forall|k: int, l: int| 0 <= k < i && 0 <= l < 8 ==> 
                    #[trigger] result@[(k * 8 + l)] == ((a@[k] as int) / pow(2, (7 - l) as nat)) % 2,
                forall|l: int| 0 <= l < j ==> 
                    #[trigger] result@[i * 8 + l] == bits_seq[l],
            decreases 8 - j
        {
            result.push(bits_seq[j]);
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}