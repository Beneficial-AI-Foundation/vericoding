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
/* helper modified by LLM (iteration 5): fix integer type inference in spec functions */
spec fn spec_pow10(exp: nat) -> nat
    decreases exp,
{
    if exp == 0 {
        1nat
    } else {
        10nat * spec_pow10((exp - 1) as nat)
    }
}

proof fn list_to_nat_recursive(l: Seq<u32>, carry: u32) -> (res: (Seq<u32>, u32))
    requires
        forall|i: int| 0 <= i < l.len() ==> l[i] < 10,
        carry < 10,
    ensures
        list_to_nat(res.0) + (res.1 as nat) == list_to_nat(l) + (carry as nat),
        res.1 < 10,
        forall|i: int| 0 <= i < res.0.len() ==> res.0[i] < 10,
    decreases l.len(),
{
    if l.len() == 0 {
        (seq![carry], 0u32)
    } else {
        let (rest_digits, rest_carry) = list_to_nat_recursive(l.subrange(1, l.len() as int), carry);
        let current_sum = l[0] + rest_carry;
        let new_digit = current_sum % 10;
        let new_carry = current_sum / 10;
        (rest_digits.insert(0, new_digit as u32), new_carry as u32)
    }
}

proof fn list_to_nat_append_lemma(l1: Seq<u32>, l2: Seq<u32>)
    requires
        forall|i: int| 0 <= i < l1.len() ==> l1[i] < 10,
        forall|i: int| 0 <= i < l2.len() ==> l2[i] < 10,
    ensures
        list_to_nat(l1 + l2) == list_to_nat(l1) + list_to_nat(l2) * (spec_pow10(l1.len()) as nat),
    decreases l1.len(),
{
    if l1.len() == 0 {
        assert(l1 + l2 == l2);
        assert(list_to_nat(l1) == 0);
        assert(spec_pow10(0) == 1);
    } else {
        let rest = l1.subrange(1, l1.len() as int);
        list_to_nat_append_lemma(rest, l2);
        assert(l1 + l2 == seq![l1[0]] + (rest + l2));
        assert(list_to_nat(l1 + l2) == l1[0] as nat + 10nat * list_to_nat(rest + l2));
        assert(list_to_nat(rest + l2) == list_to_nat(rest) + list_to_nat(l2) * (spec_pow10(rest.len()) as nat));
        assert(list_to_nat(l1) == l1[0] as nat + 10nat * list_to_nat(rest));
        assert(spec_pow10(rest.len()) * 10 == spec_pow10(l1.len()));
    }
}

proof fn carry_lemma(l: Seq<u32>, carry: u32, exp: nat)
    requires
        forall|i: int| 0 <= i < l.len() ==> l[i] < 10,
        carry < 10,
    ensures
        list_to_nat(l + seq![carry]) == list_to_nat(l) + (carry as nat) * spec_pow10(l.len()),
    decreases l.len(),
{
    if l.len() == 0 {
        assert(l + seq![carry] == seq![carry]);
        assert(list_to_nat(seq![carry]) == carry as nat);
        assert(spec_pow10(0) == 1);
    } else {
        let rest = l.subrange(1, l.len() as int);
        carry_lemma(rest, carry, exp);
        assert(l + seq![carry] == seq![l[0]] + (rest + seq![carry]));
        assert(list_to_nat(l + seq![carry]) == l[0] as nat + 10nat * list_to_nat(rest + seq![carry]));
        assert(list_to_nat(rest + seq![carry]) == list_to_nat(rest) + (carry as nat) * spec_pow10(rest.len()));
        assert(list_to_nat(l) == l[0] as nat + 10nat * list_to_nat(rest));
        assert(spec_pow10(rest.len()) * 10 == spec_pow10(l.len()));
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
/* code modified by LLM (iteration 5): fix type annotation in decreases clause */
{
    let mut result: Vec<u32> = Vec::new();
    let mut carry = 0u32;
    let mut i = 0usize;
    let max_len = if l1.len() > l2.len() { l1.len() } else { l2.len() };
    
    while i < max_len || carry > 0
        invariant
            i <= max_len,
            carry < 10,
            forall|j: int| 0 <= j < result.len() ==> result[j] < 10,
            list_to_nat(result@) + (carry as nat) * spec_pow10(result.len() as nat) == 
                list_to_nat(l1@.subrange(0, i as int)) + list_to_nat(l2@.subrange(0, i as int)),
        decreases max_len as int - i as int + (if carry > 0 { 1 } else { 0 }),
    {
        let digit1 = if i < l1.len() { l1[i] } else { 0u32 };
        let digit2 = if i < l2.len() { l2[i] } else { 0u32 };
        let sum = digit1 + digit2 + carry;
        let new_digit = sum % 10;
        carry = sum / 10;
        result.push(new_digit);
        i += 1;
    }
    
    if result.len() > 1 && result[result.len() - 1] == 0 {
        result.pop();
    }
    
    result
}
// </vc-code>

}
fn main() {}