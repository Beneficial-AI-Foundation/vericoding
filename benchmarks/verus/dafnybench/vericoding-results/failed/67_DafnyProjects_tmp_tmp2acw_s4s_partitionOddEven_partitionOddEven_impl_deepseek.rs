use vstd::prelude::*;

verus! {

// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.

spec fn odd(n: nat) -> bool { n % 2 == 1 }
spec fn even(n: nat) -> bool { n % 2 == 0 }

// <vc-helpers>
spec fn partition_point(a: Seq<nat>, i: int) -> bool {
    forall|k: int| 0 <= k < i ==> odd(a[k])
}

proof fn lemma_partition_preserves_multiset(a: Seq<nat>, b: Seq<nat>)
    requires
        b.to_multiset() == a.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < b.len() ==> !(even(b[i]) && odd(b[j]))
    ensures
        forall|i: int, j: int| 0 <= i < j < b.len() ==> !(even(b[i]) && odd(b[j]))
{
}

proof fn lemma_sorted_separation(a: Seq<nat>)
    requires
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !(even(a[i]) && odd(a[j]))
    ensures
        exists|p: int| 
            0 <= p <= a.len() &&
            (forall|i: int| 0 <= i < p ==> odd(a[i])) &&
            (forall|i: int| p <= i < a.len() ==> even(a[i]))
{
}

proof fn lemma_odd_mod(n: nat)
    ensures
        odd(n) == ((n % 2) == 1)
{
    assert(n % 2 == 0 || n % 2 == 1);
}

proof fn lemma_even_mod(n: nat)
    ensures
        even(n) == ((n % 2) == 0)
{
    assert(n % 2 == 0 || n % 2 == 1);
}

proof fn lemma_nat_to_int_conversion(n: nat)
    ensures
        (n % 2) as int == 1 ==> n % 2 == 1,
        (n % 2) as int == 0 ==> n % 2 == 0
{
}

proof fn lemma_nat_mod_constraints(n: nat)
    ensures
        n % 2 == 0 || n % 2 == 1
{
}

spec fn is_odd(n: nat) -> bool 
    ensures
        result == (n % 2 == 1)
{
    n % 2 == 1
}
// </vc-helpers>

// <vc-spec>
fn partitionOddEven(a: &mut Vec<nat>)
    ensures 
        a@.to_multiset() == old(a)@.to_multiset(),
        !(exists|i: int, j: int| 0 <= i < j < a@.len() && even(a@[i]) && odd(a@[j])),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut j: usize = 0;
    let n = a.len();
    
    while j < n
        invariant
            0 <= i <= j <= n,
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|k: int| 0 <= k < i ==> odd(a@[k]),
            forall|k: int| i <= k < j ==> even(a@[k]),
            forall|k: int, l: int| 0 <= k < i <= l < j ==> !(even(a@[k]) && odd(a@[l]))
    {
        let current = a[j];
        proof {
            lemma_nat_mod_constraints(current);
        }
        if current % 2 == 1 {
            a.swap(i, j);
            i += 1;
        }
        j += 1;
    }
    
    proof {
        lemma_partition_preserves_multiset(old(a)@, a@);
        lemma_sorted_separation(a@);
    }
}
// </vc-code>

fn main() {}

}