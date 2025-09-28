use vstd::prelude::*;

verus! {

// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.

spec fn odd(n: nat) -> bool { n % 2 == 1 }
spec fn even(n: nat) -> bool { n % 2 == 0 }

// <vc-helpers>
lemma_auto spec fn verifies_odd_even_properties(n: nat)
    ensures
        odd(n) || even(n),
        !(odd(n) && even(n)),
{
    assert(n % 2 == 0 || n % 2 == 1);
    assert(! (n % 2 == 1 && n % 2 == 0));
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
    let mut left = 0;
    let mut right = a.len() as int - 1;

    let a_multiset = a@.to_multiset();

    while left <= right
        invariant
            0 <= left <= a.len(),
            -1 <= right < a.len(),
            left <= right + 1,
            a@.to_multiset() == a_multiset,
            // All elements before `left` are odd
            forall|x: int| 0 <= x < left ==> odd(a@[x]),
            // All elements after `right` are even
            forall|x: int| right < x < a@.len() ==> even(a@[x]),
            // No even element before `left` and no odd element after `right`
            forall|x: int, y: int|
                #![trigger odd(a@[x]), even(a@[y])]
                0 <= x < left && right < y < a@.len() ==> odd(a@[x]) && even(a@[y]),
    {
        proof {
            verifies_odd_even_properties(a@[left]);
            if left <= right { // Only assert if these indices are valid
                verifies_odd_even_properties(a@[right]);
            }
        }

        if odd(a@[left]) {
            left = left + 1;
        } else if even(a@[right]) {
            right = right - 1;
        } else {
            // Swap a[left] and a[right]
            let temp = a@[left];
            a.set(left, a@[right]);
            a.set(right, temp);

            left = left + 1;
            right = right - 1;
        }
    }

    assert forall|i: int, j: int| 0 <= i < j < a@.len() implies !(even(a@[i]) && odd(a@[j])) by {
        // Based on the loop invariant, after the loop terminates, we have `left > right`.
        // This means the array is partitioned into three conceptual sections:
        // 1. `[0, left)`: all elements are odd.
        // 2. `(right, a.len())`: all elements are even.
        // 3. `[left, right]`: this range is empty because `left > right`.

        // Case 1: `i` is in the odd section.
        if i < left {
            // If `i` is in the odd section, then `a@[i]` is odd.
            // An odd number cannot be `even(a@[i])`, so `!(even(a@[i]) && odd(a@[j]))` inherently holds.
            // We just need to show `odd(a@[i])`.
            assert(0 <= i < left);
            verifies_odd_even_properties(a@[i]);
            assert(odd(a@[i]));
        }
        // Case 2: `i` is in the even section.
        else if i > right {
            // If `i` is in the even section, then `a@[i]` is even.
            // If `j` is also in the even section, then `a@[j]` is even.
            // So `even(a@[i]) && odd(a@[j])` becomes `even(a@[i]) && even(a@[j])`, which is false.
            // If `j` is in the odd section, this is a contradiction because `j > i` but `j < left` and `i > right` and `left > right`.
            // So `j` must be in the even section too.
            assert(right < i < a@.len());
            verifies_odd_even_properties(a@[i]);
            assert(even(a@[i]));

            assert(j > i);
            assert(j < a@.len());
            assert(j > right); // Since j > i and i > right
            verifies_odd_even_properties(a@[j]);
            assert(even(a@[j])); // All elements after right are even
        }
        // Case 3: `i` is in the middle section `[left, right]`.
        // This section is empty because `left > right` after loop termination.
        // So this case cannot happen: `left <= i <= right` implies `left <= right`, a contradiction.
        else {
            assert(false); // This branch is unreachable
        }
    };
}
// </vc-code>

fn main() {}

}