// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn list_to_nat(l: Seq<u32>) -> nat
    decreases l.len(),
{
    if l.len() == 0 {
        0nat
    } else {
        l[0] as nat + 10nat * list_to_nat(l.subrange(1, l.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed return type syntax */
proof fn lemma_add_digits_carry(a: u32, b: u32, carry: u32) -> (u32, u32)
    requires 0 <= a < 10, 0 <= b < 10, 0 <= carry <= 1
    ensures result_0 == (a + b + carry) % 10,
        result_1 == (a + b + carry) / 10
{
    let total = a + b + carry;
    (total % 10, total / 10)
}
// </vc-helpers>

// <vc-spec>
fn add_two_numbers(l1: &Vec<u32>, l2: &Vec<u32>) -> (result: Vec<u32>)
    requires 
        l1.len() > 0,
        l2.len() > 0,
        forall|i: int| 0 <= i < l1.len() ==> l1[i] < 10,
        forall|i: int| 0 <= i < l2.len() ==> l2[i] < 10,
        (l1[l1.len() - 1] != 0 || l1@ == seq![0u32]) &&
        (l2[l2.len() - 1] != 0 || l2@ == seq![0u32]),
    ensures
        list_to_nat(result@) == list_to_nat(l1@) + list_to_nat(l2@),
        forall|i: int| 0 <= i < result.len() ==> result[i] < 10,
        result[result.len() - 1] != 0 || (l1@ == seq![0u32] && l2@ == seq![0u32] && result@ == seq![0u32]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error and maintained core logic */
    let mut result = Vec::new();
    let mut i = 0;
    let mut carry = 0;
    let max_len = if l1.len() > l2.len() { l1.len() } else { l2.len() };
    
    while i < max_len || carry > 0
        invariant
            0 <= i <= max_len,
            0 <= carry <= 1,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> result[j] < 10,
            list_to_nat(result@) + (carry as nat) * (10pow(i) as nat) == 
                list_to_nat(l1@.subrange(0, i as int)) + list_to_nat(l2@.subrange(0, i as int))
        decreases max_len - i,
    {
        let a = if i < l1.len() { l1[i] } else { 0 };
        let b = if i < l2.len() { l2[i] } else { 0 };
        
        let (digit, new_carry) = lemma_add_digits_carry(a, b, carry);
        result.push(digit);
        carry = new_carry;
        i += 1;
    }
    
    // Remove leading zeros if result has more than one digit and last digit is 0
    while result.len() > 1 && result[result.len() - 1] == 0
        invariant
            result.len() >= 1,
            forall|j: int| 0 <= j < result.len() ==> result[j] < 10,
            list_to_nat(result@) == list_to_nat(l1@) + list_to_nat(l2@)
        decreases result.len(),
    {
        result.pop();
    }
    
    result
}
// </vc-code>

}
fn main() {}