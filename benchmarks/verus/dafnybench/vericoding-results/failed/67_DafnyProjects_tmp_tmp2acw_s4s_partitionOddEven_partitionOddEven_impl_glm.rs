use vstd::prelude::*;

verus! {

// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.

spec fn odd(n: nat) -> bool { n % 2 == 1 }
spec fn even(n: nat) -> bool { n % 2 == 0 }

// <vc-helpers>
proof fn lemma_even_or_odd(n: nat)
    ensures even(n) || odd(n)
{
    if n % 2 == 0 {
        assert(even(n));
    } else {
        assert(odd(n));
    }
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
    let n = a.len();
    if n == 0 {
        return;
    }
    let mut i = 0;
    let mut j = n - 1;

    while i <= j
        invariant
            0 <= i <= j+1 <= n,
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|k: int| 0 <= k < i ==> odd(a@[k]),
            forall|k: int| j < k < n ==> even(a@[k]),
    {
        if odd(a[i]) {
            i += 1;
        } else if even(a[j]) {
            j -= 1;
        } else {
            a.swap(i, j);
            i += 1;
            j -= 1;
        }
    }
}
// </vc-code>

fn main() {}

}