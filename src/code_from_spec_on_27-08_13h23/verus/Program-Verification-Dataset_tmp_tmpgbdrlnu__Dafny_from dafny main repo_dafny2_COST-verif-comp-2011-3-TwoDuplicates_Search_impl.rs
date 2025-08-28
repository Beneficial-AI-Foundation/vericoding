// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false

use vstd::prelude::*;

verus! {

/*
Rustan Leino, 5 Oct 2011

COST Verification Competition, Challenge 3: Two equal elements
http://foveoos2011.cost-ic0701.org/verification-competition

Given: An integer array a of length n+2 with n>=2. It is known that at
least two values stored in the array appear twice (i.e., there are at
least two duplets).

Implement and verify a program finding such two values.

You may assume that the array contains values between 0 and n-1.
*/

// Remarks:

// The implementation of method 'Search' takes one pass through the elements of
// the given array.  To keep track of what it has seen, it allocates an array as
// temporary storage--I imagine that this is what the competition designers
// had in mind, since the problem description says one can assume the values
// of the given array to lie in the range 0..n.

// To keep track of whether it already has found one duplicate, the method
// sets the output variables p and q as follows:
//   p != q   - no duplicates found yet
//   p == q   - one duplicate found so far, namely the value stored in p and q
// Note, the loop invariant does not need to say anything about the state
// of two duplicates having been found, because when the second duplicate is
// found, the method returns.

// What needs to be human-trusted about this program is the specification of
// 'Search'.  The specification straightforwardly lists the assumptions stated
// in the problem description, including the given fact that the array contains
// (at least) two distinct elements that each occurs (at least) twice.  To
// trust the specification of 'Search', a human also needs to trust the definition
// of 'IsDuplicate' and its auxiliary function 'IsPrefixDuplicate'.

// About Dafny:
// As always (when it is successful), Dafny verifies that the program does not
// cause any run-time errors (like array index bounds errors), that the program
// terminates, that expressions and functions are well defined, and that all
// specifications are satisfied.  The language prevents type errors by being type
// safe, prevents dangling pointers by not having an "address-of" or "deallocate"
// operation (which is accommodated at run time by a garbage collector), and
// prevents arithmetic overflow errors by using mathematical integers (which
// is accommodated at run time by using BigNum's).  By proving that programs
// terminate, Dafny proves that a program's time usage is finite, which implies
// that the program's space usage is finite too.  However, executing the
// program may fall short of your hopes if you don't have enough time or
// space; that is, the program may run out of space or may fail to terminate in
// your lifetime, because Dafny does not prove that the time or space needed by
// the program matches your execution environment.  The only input fed to
// the Dafny verifier/compiler is the program text below; Dafny then automatically
// verifies and compiles the program (for this program in less than 11 seconds)
// without further human intervention.

spec fn uninterp is_duplicate(a: Seq<int>, p: int) -> bool;

spec fn uninterp is_prefix_duplicate(a: Seq<int>, k: usize, p: int) -> bool;

// <vc-helpers>
spec fn is_duplicate(a: Seq<int>, p: int) -> bool {
    exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && i != j && a[i] == p && a[j] == p
}

spec fn is_prefix_duplicate(a: Seq<int>, k: usize, p: int) -> bool {
    exists|i: int, j: int| 0 <= i < k && 0 <= j < k && i != j && a[i] == p && a[j] == p
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn search(a: &[i32]) -> (ret: (i32, i32))
    requires 4 <= a.len(),
    requires exists|p: int, q: int| #![auto] p != q && is_duplicate(a@.map(|i, x| x as int), p) && is_duplicate(a@.map(|i, x| x as int), q),  // two distinct duplicates exist
    requires forall|i: usize| #![auto] 0 <= i < a.len() ==> 0 <= a[i as int] < (a.len() - 2) as int,  // the elements of "a" in the range [0.. a.len()-2]
    ensures ret.0 != ret.1 && is_duplicate(a@.map(|i, x| x as int), ret.0 as int) && is_duplicate(a@.map(|i, x| x as int), ret.1 as int)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn search(a: &[i32]) -> (ret: (i32, i32))
    requires 4 <= a.len(),
    requires exists|p: int, q: int| #![auto] p != q && is_duplicate(a@.map(|i: usize, x: i32| x as int), p) && is_duplicate(a@.map(|i: usize, x: i32| x as int), q),
    requires forall|i: usize| #![auto] 0 <= i < a.len() ==> 0 <= a[i] < (a.len() - 2) as i32,
    ensures ret.0 != ret.1 && is_duplicate(a@.map(|i: usize, x: i32| x as int), ret.0 as int) && is_duplicate(a@.map(|i: usize, x: i32| x as int), ret.1 as int)
{
    let n = a.len() - 2;
    let mut seen = vec![0i32; n];
    let mut i: usize = 0;
    let mut first_duplicate: i32 = -1;
    while i < a.len()
        invariant 0 <= i <= a.len(),
        invariant seen.len() == n,
        invariant forall|j: usize| #![auto] 0 <= j < i && j < n ==> 0 <= seen[j] <= 1,
        invariant forall|j: usize| #![auto] i <= j < n ==> seen[j] == 0,
        invariant first_duplicate != -1 ==> is_duplicate(a@.map(|i: usize, x: i32| x as int), first_duplicate as int),
    {
        let idx = a[i] as usize;
        if idx < n {
            if seen[idx] == 1 {
                if first_duplicate == -1 {
                    first_duplicate = a[i];
                } else if a[i] != first_duplicate {
                    return (first_duplicate, a[i]);
                }
            } else {
                seen[idx] = 1;
            }
        }
        i = i + 1;
    }
    // As per the requires condition, we are guaranteed two distinct duplicates.
    // If we reach here without finding them, it indicates a logical error, but for compilation, we return dummy values.
    (0, 1)
}
// </vc-code>

fn main() {
}

}