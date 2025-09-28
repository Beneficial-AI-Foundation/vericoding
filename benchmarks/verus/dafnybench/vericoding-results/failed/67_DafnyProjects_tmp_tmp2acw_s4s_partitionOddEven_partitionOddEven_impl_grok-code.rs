use vstd::prelude::*;

verus! {

// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.

spec fn odd(n: nat) -> bool { n % 2 == 1 }
spec fn even(n: nat) -> bool { n % 2 == 0 }

// <vc-helpers>
verus! {

pub exec fn odd_exec(n: nat) -> (res: bool)
    ensures res == odd(n)
{
    n % 2 == 1
}

pub exec fn even_exec(n: nat) -> (res: bool)
    ensures res == even(n)
{
    n % 2 == 0
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
    let mut i: usize = 0;
    let mut j: usize = a.len() - 1;
    while i < j
        invariant
            i <= j + 1,
            forall |k: int| 0 <= k < i ==> odd(a@[k]),
            forall |k: int| j < k < (a.len() as int) ==> even(a@[k]),
    {
        while i < j && odd_exec(a[i])
            invariant
                i <= j + 1,
                forall |k: int| 0 <= k < i ==> odd(a@[k]),
                forall |k: int| j < k < (a.len() as int) ==> even(a@[k]),
        {
            i += 1;
        }
        while i < j && even_exec(a[j])
            invariant
                i <= j + 1,
                forall |k: int| 0 <= k < i ==> odd(a@[k]),
                forall |k: int| j < k < (a.len() as int) ==> even(a@[k]),
        {
            j -= 1;
        }
        if i < j {
            let temp = a[i];
            a[i] = a[j];
            a[j] = temp;
            proof {
                assert(forall |k: int| 0 <= k <= i ==> odd(a@[k]));
                assert(forall |k: int| (j as int) <= k < (a.len() as int) ==> even(a@[k]));
            }
            i += 1;
            j -= 1;
        }
    }
}
// </vc-code>

fn main() {}

}