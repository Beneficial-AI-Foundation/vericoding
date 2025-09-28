use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

spec fn is_odd(n: int) -> bool {
    n % 2 != 0
}

// <vc-helpers>
// No helper functions needed for this proof.
// </vc-helpers>

// <vc-spec>
fn first_even_odd_difference(a: &[i32]) -> (diff: i32)
    requires 
        a.len() >= 2,
        exists|i: int| 0 <= i < a.len() && is_even(a[i] as int),
        exists|i: int| 0 <= i < a.len() && is_odd(a[i] as int),
    ensures 
        exists|i: int, j: int| 
            0 <= i < a.len() && 
            0 <= j < a.len() && 
            is_even(a[i] as int) && 
            is_odd(a[j] as int) && 
            diff == a[i] - a[j] && 
            (forall|k: int| 0 <= k < i ==> is_odd(a[k] as int)) && 
            (forall|k: int| 0 <= k < j ==> is_even(a[k] as int))
// </vc-spec>
// <vc-code>
{
    let n: int = a.len() as int;
    // indices and flags
    let mut i_idx: int = 0;
    let mut j_idx: int = 0;
    let mut found_i: bool = false;
    let mut found_j: bool = false;
    let mut k: int = 0;

    while k < n
        invariant 0 <= k && k <= n;
        invariant 0 <= i_idx && i_idx <= n && 0 <= j_idx && j_idx <= n;
        invariant found_i ==> (0 <= i_idx && i_idx < n);
        invariant found_j ==> (0 <= j_idx && j_idx < n);
        invariant forall|t: int| 0 <= t < k ==>
            ( (!found_i) ==> is_odd(a[t as usize] as int) ) &&
            ( (!found_j) ==> is_even(a[t as usize] as int) );
    {
        if (!found_i && is_even(a[k as usize] as int)) {
            i_idx = k;
            found_i = true;
        }
        if (!found_j && is_odd(a[k as usize] as int)) {
            j_idx = k;
            found_j = true;
        }
        if (found_i && found_j) {
            assert(i_idx >= 0 && i_idx < n);
            assert(j_idx >= 0 && j_idx < n);
            return a[i_idx as usize] - a[j_idx as usize];
        }
        k = k + 1;
    }

    // If we reach here, the loop finished without returning; derive contradiction from preconditions.
    proof {
        // From loop exit we have k == n and not (found_i && found_j).
        assert(k == n);

        // Precondition: there exists an even and an odd index in the array.
        assert(exists|ii: int| 0 <= ii && ii < n && is_even(a[ii as usize] as int));
        assert(exists|jj: int| 0 <= jj && jj < n && is_odd(a[jj as usize] as int));

        // By the loop invariant at k == n:
        // if !found_i then forall t < n, a[t] is odd
        // if !found_j then forall t < n, a[t] is even
        if (!found_i) {
            assert(forall|t: int| 0 <= t < n ==> is_odd(a[t as usize] as int));
            // From this, there cannot exist an even element in 0..n
            assert(!exists|ii: int| 0 <= ii && ii < n && is_even(a[ii as usize] as int));
            // Contradiction with precondition
            assert(false);
        } else {
            // !found_i is false, hence found_i is true. Since we did not return, it must be that !found_j.
            assert(!found_j);
            assert(forall|t: int| 0 <= t < n ==> is_even(a[t as usize] as int));
            // From this, there cannot exist an odd element in 0..n
            assert(!exists|jj: int| 0 <= jj && jj < n && is_odd(a[jj as usize] as int));
            // Contradiction with precondition
            assert(false);
        }
    }

    // unreachable, but satisfy return type
    0
}
// </vc-code>

fn main() {
}

}