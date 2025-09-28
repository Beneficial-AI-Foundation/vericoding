// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lemma_pow_mult_lt_max(x: nat, e1: nat, e2: nat) 
    requires e1 < 8, e2 < 8,
    ensures 
        pow(2, e1) < 256,
        pow(2, e2) < 256,
        pow(2, e1) * pow(2, e2) < 65536
{}

/* helper modified by LLM (iteration 5): Fixed sequence indexing type mismatch */
fn unpack_byte(byte: u8) -> (bits: Vec<u8>)
    ensures 
        bits@.len() == 8,
        forall|j: int| 0 <= j < 8 ==> #[trigger] bits@[j] == ((byte as int) / pow(2, (7 - j) as nat)) % 2
{
    let mut bits = Vec::new();
    let mut shift = 7;
    while shift >= 0
        invariant
            bits@.len() == (7 - shift) as nat,
            forall|k: int| 0 <= k < bits@.len() ==> #[trigger] bits@[k] == ((byte as int) / pow(2, (7 - k) as nat)) % 2,
        decreases shift
    {
        let bit = ((byte >> shift) & 1) as u8;
        bits.push(bit);
        shift = shift - 1;
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
{
    /* code modified by LLM (iteration 5): Fixed sequence indexing type mismatch in inner loop */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result@.len() == (i as int) * 8,
            forall|k: int, l: int| 0 <= k < (i as int) && 0 <= l < 8 ==> #[trigger] result@[k * 8 + l] == ((a@[k] as int) / pow(2, (7 - l) as nat)) % 2,
        decreases a.len() - i
    {
        let bits = unpack_byte(a[i]);
        let mut j: usize = 0;
        while j < bits.len()
            invariant
                result@.len() == (i as int) * 8 + (j as int),
                forall|m: int| 0 <= m < (j as int) ==> #[trigger] bits@[m] == ((a@[i] as int) / pow(2, (7 - m) as nat)) % 2,
            decreases bits.len() - j
        {
            result.push(bits[j]);
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}