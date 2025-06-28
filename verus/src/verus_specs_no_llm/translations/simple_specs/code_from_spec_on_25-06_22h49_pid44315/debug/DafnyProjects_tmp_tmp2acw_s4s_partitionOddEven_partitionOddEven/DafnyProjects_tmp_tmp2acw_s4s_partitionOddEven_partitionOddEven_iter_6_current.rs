verus! {

use builtin::*;
use builtin_macros::*;

fn main() {
}

spec fn odd(n: nat) -> bool {
    n % 2 == 1
}

spec fn even(n: nat) -> bool {
    n % 2 == 0
}

// Helper lemma to prove properties about odd and even
proof fn lemma_odd_even_exclusive(n: nat)
    ensures odd(n) ==> !even(n),
    ensures even(n) ==> !odd(n),
{
    // The proof is automatic for this simple case
}

// Helper lemma to prove that every natural number is either odd or even
proof fn lemma_odd_or_even(n: nat)
    ensures odd(n) || even(n),
{
    // The proof is automatic for this simple case
}

}