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
/* helper modified by LLM (iteration 5): fixed proof logic for append and prepend lemmas */
use vstd::arithmetic::power::pow;

proof fn list_to_nat_append(prefix: Seq<u32>, suffix: Seq<u32>)
    requires
        forall|i: int| 0 <= i < prefix.len() ==> prefix[i] < 10,
        forall|i: int| 0 <= i < suffix.len() ==> suffix[i] < 10,
    ensures
        list_to_nat(prefix + suffix) == list_to_nat(prefix) + pow(10, prefix.len()) * list_to_nat(suffix),
    decreases prefix.len(),
{
    if prefix.len() == 0 {
        assert(prefix + suffix =~= suffix);
        assert(list_to_nat(prefix) == 0nat);
        assert(pow(10, 0) == 1nat);
    } else {
        let first = prefix[0];
        let rest_prefix = prefix.subrange(1, prefix.len() as int);
        list_to_nat_append(rest_prefix, suffix);
        assert((prefix + suffix).subrange(1, (prefix + suffix).len() as int) =~= rest_prefix + suffix);
    }
}

proof fn list_to_nat_single(digit: u32)
    requires digit < 10,
    ensures list_to_nat(seq![digit]) == digit as nat,
{
    assert(seq![digit].subrange(1, 1) =~= seq![]);
    assert(list_to_nat(seq![]) == 0nat);
}

proof fn list_to_nat_prepend(digit: u32, rest: Seq<u32>)
    requires
        digit < 10,
        forall|i: int| 0 <= i < rest.len() ==> rest[i] < 10,
    ensures
        list_to_nat(seq![digit] + rest) == digit as nat + 10nat * list_to_nat(rest),
{
    if rest.len() == 0 {
        assert(seq![digit] + rest =~= seq![digit]);
        list_to_nat_single(digit);
    } else {
        assert((seq![digit] + rest).subrange(1, (seq![digit] + rest).len() as int) =~= rest);
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
    /* code modified by LLM (iteration 5): fixed overflow issues and carry bounds */
    let mut result: Vec<u32> = Vec::new();
    let mut carry = 0u32;
    let mut i = 0;
    
    while i < l1.len() || i < l2.len() || carry > 0
        invariant
            carry <= 1,
            forall|j: int| 0 <= j < result.len() ==> result[j] < 10,
            result.len() == i,
            i <= l1.len() && i <= l2.len(),
        decreases (l1.len() + l2.len()) as int - i + carry as int,
    {
        let digit1 = if i < l1.len() { l1[i] } else { 0u32 };
        let digit2 = if i < l2.len() { l2[i] } else { 0u32 };
        
        assert(digit1 < 10 && digit2 < 10 && carry <= 1);
        assert(digit1 + digit2 <= 18);
        assert(digit1 + digit2 + carry <= 19);
        
        let sum = digit1 + digit2 + carry;
        
        result.push(sum % 10);
        carry = sum / 10;
        
        assert(carry <= 1);
        i += 1;
    }
    
    if result.len() == 0 {
        result.push(0);
    }
    
    result
}
// </vc-code>

}
fn main() {}