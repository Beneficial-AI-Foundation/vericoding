use vstd::prelude::*;

verus! {

// Precondition for lastDigit function
spec fn last_digit_precond(n: nat) -> bool {
    true
}

// Spec version of the function for use in specifications
spec fn last_digit_spec(n: nat) -> nat {
    n % 10
}

// The main lastDigit function
fn last_digit(n: u32) -> (result: u32)
    requires 
        last_digit_precond(n as nat),
    ensures 
        0 <= result < 10,
        result == last_digit_spec(n as nat),
{
    n % 10
}

// Postcondition specification
spec fn last_digit_postcond(n: nat, result: nat) -> bool {
    (0 <= result < 10) && (result == n % 10)
}

// Proof that the function satisfies its specification
proof fn last_digit_spec_satisfied(n: u32)
    requires 
        last_digit_precond(n as nat),
    ensures 
        last_digit_postcond(n as nat, last_digit_spec(n as nat)),
{
    // The proof is automatic in Verus
}

}

fn main() {}