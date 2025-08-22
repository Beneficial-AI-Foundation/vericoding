use vstd::prelude::*;

verus! {

// Helper function to compute sum of digits
spec fn sum_of_digits(x: nat) -> nat 
    decreases x
{
    if x == 0 { 0nat } else { (x % 10) + sum_of_digits(x / 10) }
}

// Executable version of sum_of_digits using exec mode
#[verifier::external_body]
fn sum_of_digits_exec(x: u32) -> (result: u32)
    ensures result == sum_of_digits(x as nat)
{
    return 0;  // TODO: Remove this line and implement the function body
}

// Precondition
spec fn count_sum_divisible_by_precond(n: nat, d: nat) -> bool {
    d > 0
}

// Helper function to check if sum of digits is divisible by d
spec fn is_sum_divisible_by(x: nat, d: nat) -> bool
    recommends d > 0
{
    sum_of_digits(x) % d == 0
}

// Executable version
fn is_sum_divisible_by_exec(x: u32, d: u32) -> (result: bool)
    requires d > 0
    ensures result == is_sum_divisible_by(x as nat, d as nat)
{
    return false;  // TODO: Remove this line and implement the function body
}

// Spec function to count numbers less than n whose digit sum is divisible by d
spec fn count_sum_divisible_by_spec(n: nat, d: nat) -> nat 
    recommends d > 0
    decreases n
{
    if n == 0 { 
        0nat
    } else {
        let prev = (n - 1) as nat;
        count_sum_divisible_by_spec(prev, d) + 
        (if is_sum_divisible_by(prev, d) { 1nat } else { 0nat })
    }
}

// Main function using external body to avoid complex invariants
#[verifier::external_body]
fn count_sum_divisible_by(n: u32, d: u32) -> (result: u32)
    requires count_sum_divisible_by_precond(n as nat, d as nat)
    ensures result == count_sum_divisible_by_spec(n as nat, d as nat)
{
    return 0;  // TODO: Remove this line and implement the function body
}

// Postcondition matches the original Lean specification
spec fn count_sum_divisible_by_postcond(n: nat, d: nat, result: nat) -> bool {
    count_sum_divisible_by_precond(n, d) ==> 
    result == count_sum_divisible_by_spec(n, d)
}

// Proof that the function satisfies its specification
proof fn count_sum_divisible_by_spec_satisfied(n: u32, d: u32)
    requires count_sum_divisible_by_precond(n as nat, d as nat)
    ensures count_sum_divisible_by_postcond(n as nat, d as nat, count_sum_divisible_by_spec(n as nat, d as nat))
{
    assume(false);  // TODO: Remove this line and implement the proof
}

fn main() {
    // TODO: Remove this comment and implement the function body
}

} // verus!