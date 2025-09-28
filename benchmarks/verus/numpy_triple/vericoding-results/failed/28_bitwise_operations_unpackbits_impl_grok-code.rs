// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): kept empty as no helper needed */
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
/* code modified by LLM (iteration 5): changed invariants to forall ii,jj directly to avoid exists quantifier and trigger issues */
    let mut result: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result@.len() == i as int * 8,
            forall |ii: int, jj: int| 0 <= ii < i as int && 0 <= jj < 8 ==>
                #[trigger] result@[ii * 8 + jj] == ((a@[ii] as int) / pow(2, (7 - jj) as nat)) % 2,
        decreases a@.len() - i as int
    {
        let byte: u8 = a[i];
        let mut j: usize = 0;
        while j < 8
            invariant
                result@.len() == i as int * 8 + j as int,
                forall |ii: int, jj: int| (0 <= ii < i as int && 0 <= jj < 8) || (ii == i as int && 0 <= jj < j as int) ==>
                    #[trigger] result@[ii * 8 + jj] == ((a@[ii] as int) / pow(2, (7 - jj) as nat)) % 2,
                i < a.len(),
            decreases 8 - j as int
        {
            let shift: usize = 7 - j;
            let bit_val: u32 = ((byte as u32) >> shift) & 1;
            let bit: u8 = bit_val as u8;
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