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
proof fn lemma_list_to_nat_single(d: u32)
    requires d < 10
    ensures list_to_nat(seq![d]) == d as nat
{
    assert(seq![d].subrange(1, 1) =~= Seq::<u32>::empty());
}

proof fn lemma_list_to_nat_append(l: Seq<u32>, d: u32)
    requires d < 10
    ensures list_to_nat(l.push(d)) == list_to_nat(l) + (d as nat) * pow10(l.len() as nat)
    decreases l.len()
{
    if l.len() == 0 {
        lemma_list_to_nat_single(d);
        assert(list_to_nat(seq![d]) == d as nat);
    } else {
        assert(l.push(d).subrange(1, (l.len() + 1) as int) =~= l.subrange(1, l.len() as int).push(d));
        lemma_list_to_nat_append(l.subrange(1, l.len() as int), d);
    }
}

spec fn pow10(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1nat
    } else {
        10nat * pow10((n - 1) as nat)
    }
}

proof fn lemma_pow10_positive(n: nat)
    ensures pow10(n) > 0
    decreases n
{
    if n != 0 {
        lemma_pow10_positive((n - 1) as nat);
    }
}

proof fn lemma_list_to_nat_bound(l: Seq<u32>)
    requires forall|i: int| 0 <= i < l.len() ==> l[i] < 10
    ensures list_to_nat(l) < pow10(l.len() as nat)
    decreases l.len()
{
    if l.len() > 0 {
        lemma_list_to_nat_bound(l.subrange(1, l.len() as int));
        if l.len() == 1 {
            assert(list_to_nat(l) == l[0] as nat);
        }
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
    let mut carry: u32 = 0;
    let mut i: usize = 0;
    
    while i < l1.len() || i < l2.len() || carry > 0
        invariant
            i <= l1.len() || i <= l2.len(),
            carry < 10,
            forall|j: int| 0 <= j < result.len() ==> result[j] < 10,
            list_to_nat(result@) + (carry as nat) * pow10(result.len() as nat) == 
                list_to_nat(l1@.subrange(0, min(i as int, l1.len() as int))) + 
                list_to_nat(l2@.subrange(0, min(i as int, l2.len() as int))),
    {
        let d1 = if i < l1.len() { l1[i] } else { 0 };
        let d2 = if i < l2.len() { l2[i] } else { 0 };
        let sum = d1 + d2 + carry;
        let digit = sum % 10;
        carry = sum / 10;
        
        proof {
            lemma_list_to_nat_append(result@, digit);
            if i < l1.len() {
                assert(l1@.subrange(0, (i + 1) as int) =~= l1@.subrange(0, i as int).push(l1[i]));
                lemma_list_to_nat_append(l1@.subrange(0, i as int), l1[i]);
            }
            if i < l2.len() {
                assert(l2@.subrange(0, (i + 1) as int) =~= l2@.subrange(0, i as int).push(l2[i]));
                lemma_list_to_nat_append(l2@.subrange(0, i as int), l2[i]);
            }
        }
        
        result.push(digit);
        i = i + 1;
    }
    
    while result.len() > 1 && result[result.len() - 1] == 0
        invariant
            result.len() >= 1,
            forall|j: int| 0 <= j < result.len() ==> result[j] < 10,
            list_to_nat(result@) == list_to_nat(l1@) + list_to_nat(l2@),
    {
        result.pop();
    }
    
    result
}
// </vc-code>

}
fn main() {}