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
/* helper modified by LLM (iteration 5): convert nat to digits sequence least-significant-first */
spec fn nat_to_digits(n: nat) -> Seq<u32>
    decreases n
{
    if n == 0 {
        seq![0u32]
    } else if n < 10 {
        seq![n as u32]
    } else {
        seq![(n % 10) as u32] + nat_to_digits(n / 10)
    }
}

spec fn pow10(k: nat) -> nat
    decreases k
{
    if k == 0 {
        1nat
    } else {
        10nat * pow10(k - 1)
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
    /* code modified by LLM (iteration 5): digit-wise addition with invariant tracking partial sum using pow10 and carry */
    let mut result = Vec::<u32>::new();
    let mut carry: u32 = 0;
    let mut i: usize = 0;
    let n1: usize = l1.len();
    let n2: usize = l2.len();
    let max: usize = if n1 > n2 { n1 } else { n2 };
    while i < max
        invariant
            0 <= i as int,
            i as int <= max as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] < 10,
            carry <= 1u32,
            list_to_nat(result@) + pow10(i as nat) * (list_to_nat(l1@.subrange(i as int, n1 as int)) + list_to_nat(l2@.subrange(i as int, n2 as int))) + (carry as nat) * pow10(i as nat) == list_to_nat(l1@) + list_to_nat(l2@),
        decreases (max - i) as int
    {
        let d1: u32 = if i < n1 { l1[i] } else { 0u32 };
        let d2: u32 = if i < n2 { l2[i] } else { 0u32 };
        let s: u32 = d1 + d2 + carry;
        proof {
            // bring the loop invariant into scope
            assert(list_to_nat(result@) + pow10(i as nat) * (list_to_nat(l1@.subrange(i as int, n1 as int)) + list_to_nat(l2@.subrange(i as int, n2 as int))) + (carry as nat) * pow10(i as nat) == list_to_nat(l1@) + list_to_nat(l2@));
            // decompose the remaining parts of l1 and l2 at position i
            if i < n1 {
                assert(list_to_nat(l1@.subrange(i as int, n1 as int)) == (l1[i] as nat) + 10nat * list_to_nat(l1@.subrange(i as int + 1, n1 as int)));
            } else {
                assert(list_to_nat(l1@.subrange(i as int, n1 as int)) == 0nat);
            }
            if i < n2 {
                assert(list_to_nat(l2@.subrange(i as int, n2 as int)) == (l2[i] as nat) + 10nat * list_to_nat(l2@.subrange(i as int + 1, n2 as int)));
            } else {
                assert(list_to_nat(l2@.subrange(i as int, n2 as int)) == 0nat);
            }
            // decompose the sum digit and carry'
            assert((s as nat) == (s % 10) as nat + 10nat * (s / 10) as nat);
            // From the invariant and the decompositions above we can derive the invariant for i+1 after pushing (s%10) and updating carry to (s/10)
            // The solver can combine the asserted equalities to establish the next-state equality
        }
        result.push(s % 10);
        carry = s / 10;
        i = i + 1;
    }
    if carry != 0 {
        result.push(carry);
    }
    result
}
// </vc-code>

}
fn main() {}