// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn pow2(n: nat) -> nat 
    decreases n
{
    if n == 0 {
        1nat
    } else {
        2nat * pow2((n - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Use proper ghost variable approach with sequence operations */
spec fn invert_helper(bit_width: nat, a_seq: Seq<u32>) -> Seq<u32>
    ensures
        result.len() == a_seq.len(),
        forall|i: int| 0 <= i < a_seq.len() ==> result[i] as nat == (pow2(bit_width) - 1) - (a_seq[i] as nat)
{
    if a_seq.len() == 0 {
        Seq::empty()
    } else {
        let val = (pow2(bit_width) - 1) - (a_seq[0] as nat);
        Seq::new(1, |i: int| if i == 0 { val as u32 } else { 0u32 }).add(invert_helper(bit_width, a_seq.subrange(1, a_seq.len() as int)))
    }
}

// </vc-helpers>

// <vc-spec>
fn invert(bit_width: u32, a: Vec<u32>) -> (result: Vec<u32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == (pow2(bit_width as nat) - 1) - a@[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix ghost block syntax and use proper variable handling */
    let ghost bit_width_nat = bit_width as nat;
    let mut result = Vec::<u32>::new();
    let mut index = 0;
    
    while index < a.len()
        invariant
            result@.len() == index,
            forall|i: int| 0 <= i < index ==> result@[i] as nat == (pow2(bit_width_nat) - 1) - (a@[i] as nat),
        decreases a.len() - index
    {
        let ghost a_val = a@[index] as nat;
        let ghost inverted_val = (pow2(bit_width_nat) - 1) - a_val;
        let inverted_value = inverted_val as u32;
        result.push(inverted_value);
        index += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}