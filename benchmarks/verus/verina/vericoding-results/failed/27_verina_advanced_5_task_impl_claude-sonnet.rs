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
spec fn list_to_nat_rev(l: Seq<u32>) -> nat
    decreases l.len(),
{
    if l.len() == 0 {
        0nat
    } else {
        (l[l.len() - 1] as nat) * pow(10nat, (l.len() - 1) as nat) + list_to_nat_rev(l.subrange(0, l.len() - 1))
    }
}

spec fn pow(base: nat, exp: nat) -> nat
    decreases exp,
{
    if exp == 0 {
        1nat
    } else {
        base * pow(base, exp - 1)
    }
}

proof fn list_to_nat_equiv(l: Seq<u32>)
    ensures list_to_nat(l) == list_to_nat_rev(l),
    decreases l.len(),
{
    if l.len() == 0 {
    } else if l.len() == 1 {
    } else {
        list_to_nat_equiv(l.subrange(1, l.len() as int));
        list_to_nat_equiv(l.subrange(0, l.len() - 1));
    }
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
    let mut result = Vec::new();
    let mut i1 = 0;
    let mut i2 = 0;
    let mut carry = 0u32;
    
    while i1 < l1.len() || i2 < l2.len() || carry > 0
        invariant
            0 <= i1 <= l1.len(),
            0 <= i2 <= l2.len(),
            carry <= 1,
            forall|j: int| 0 <= j < result.len() ==> result[j] < 10,
    {
        let digit1 = if i1 < l1.len() { l1[i1] } else { 0u32 };
        let digit2 = if i2 < l2.len() { l2[i2] } else { 0u32 };
        
        let sum = digit1 + digit2 + carry;
        let digit = sum % 10;
        carry = sum / 10;
        
        result.push(digit);
        
        if i1 < l1.len() {
            i1 = i1 + 1;
        }
        if i2 < l2.len() {
            i2 = i2 + 1;
        }
    }
    
    if result.len() > 1 && result[result.len() - 1] == 0 {
        result.pop();
    }
    
    if result.len() == 0 {
        result.push(0);
    }
    
    result
}
// </vc-code>

}
fn main() {}