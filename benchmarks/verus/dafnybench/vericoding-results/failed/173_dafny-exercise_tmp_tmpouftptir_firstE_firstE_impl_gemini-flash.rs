use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains_char_axiom(s: Seq<char>, c: char) -> (b: bool)
    ensures
        b == s.contains(c),
{
    // This helper is for the specification, not a runtime function
    // The `map_values` and `reduce` on `Seq` are proof-only operations.
    // We can't actually *run* this code.
    // The previous implementation was not valid Verus for this context.
    // Instead, we can define an axiom that relates `contains` to `exists`.
    s.contains(c)
}
// </vc-helpers>

// <vc-spec>
fn firstE(a: &[char]) -> (x: i32)
    ensures
        if a@.contains('e') {
            0 <= x < a@.len() && a@[x as int] == 'e' && 
            forall|i: int| 0 <= i < x ==> a@[i] != 'e'
        } else {
            x == -1
        }
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let len: usize = a.len();

    while i < len
        invariant
            0 <= i as int <= len as int,
            forall|j: int| 0 <= j < i as int ==> a@[j] != 'e',
    {
        if a[i] == 'e' {
            return i as i32;
        }
        i = i + 1;
    }

    // We've iterated through the entire array and haven't found 'e'.
    // Therefore, 'e' is not present in the array.
    proof {
        assert forall |k: int| 0 <= k < len as int implies a@[k] != 'e' by {
            // When the loop terminates, i == len.
            // The loop invariant states: forall|j: int| 0 <= j < i ==> a@[j] != 'e'
            // Substituting i with len, we get: forall|j: int| 0 <= j < len ==> a@[j] != 'e'
            // This is exactly what we need to prove for `k`.
            assert(i == len); // Loop terminates when i == len
            assert(len == a@.len());
            // The invariant holds: forall|j: int| 0 <= j < i as int ==> a@[j] != 'e',
            // which with i=len becomes forall|j: int| 0 <= j < len as int ==> a@[j] != 'e'.
            // This is the desired conclusion.
        };
        assert(!a@.contains('e')) by {
            // If a@.contains('e') were true, then there would exist some index `k`
            // such that 0 <= k < len and a@[k] == 'e'.
            // However, we just proved that forall |k: int| 0 <= k < len implies a@[k] != 'e'.
            // This is a contradiction, so a@.contains('e') must be false.
            assert forall |j: int| 0 <= j < a@.len() implies a@[j] != 'e' by {
                // This assertion directly follows from the loop invariant after termination.
                // At loop termination, i == len, so the invariant becomes
                // forall|j: int| 0 <= j < len ==> a@[j] != 'e'.
                // Since len == a@.len(), this is equivalent to
                // forall|j: int| 0 <= j < a@.len() ==> a@[j] != 'e'.
            };
            assert(!a@.contains('e')) by {
                // This assertion is directly supported by the above forall.
                // If a@.contains('e') was true, then there would be an element such that `a@[j] == 'e'`,
                // which contradicts the proven `forall`.
            }
        }
    }
    
    // As per the contract, if 'e' is not found, return -1.
    -1
}
// </vc-code>

fn main() {
}

}