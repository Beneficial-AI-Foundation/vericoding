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
/* helper modified by LLM (iteration 5): fixed syntax errors in requires and decreases clauses by removing trailing commas and simplifying, added requires for prefix_nat */
spec fn pow10(n: int) -> nat
    requires 0 <= n,
    decreases n as nat,
{
    if n == 0 {
        1nat
    } else {
        10nat * pow10(n - 1)
    }
}

spec fn prefix_nat(l: Seq<u32>, len: int) -> nat
    requires 0 <= len,
    decreases len as nat,
{
    if len <= 0 {
        0nat
    } else if len > l.len() {
        prefix_nat(l, l.len())
    } else {
        l[len - 1] as nat * pow10(len - 1) + prefix_nat(l, len - 1)
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
    /* code modified by LLM (iteration 5): implemented digit-by-digit addition with carry propagation */
    let mut result: Vec<u32> = Vec::new();
    let mut carry = 0u32;
    let len1 = l1.len();
    let len2 = l2.len();
    let max_len = if len1 >= len2 { len1 } else { len2 };
    let mut i: usize = 0usize;
    while i < max_len
        invariant
            i <= max_len,
            carry <= 1u32,
            0 <= carry,
            result.len() == i,
            forall |j: int| 0 <= j < (i as int) ==> result[j] < 10,
            prefix_nat(result@, i as int) + (carry as nat) * pow10(i as int) == prefix_nat(l1@, i as int) + prefix_nat(l2@, i as int),
        decreases max_len - i
    {
        let d1 = if i < len1 { l1[i] } else { 0u32 };
        let d2 = if i < len2 { l2[i] } else { 0u32 };
        let sum_val = d1 + d2 + carry;
        let digit = sum_val % 10;
        carry = sum_val / 10;
        result.push(digit);
        i = i + 1usize;
    }
    if carry > 0 {
        result.push(carry);
    }
    result
}
// </vc-code>

}
fn main() {}