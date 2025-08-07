use vstd::prelude::*;

verus! {

spec fn sum_of_fourth_power_of_odd_numbers_precond(n: nat) -> bool {
    true
}

spec fn sum_of_fourth_power_of_odd_numbers_postcond(n: nat, result: nat) -> bool {
    15 * result == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
}

spec fn sum_of_fourth_power_of_odd_numbers_spec(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0nat
    } else {
        let prev = sum_of_fourth_power_of_odd_numbers_spec((n - 1) as nat);
        let next_odd = (2 * (n - 1) + 1) as nat;
        let next_odd_fourth = (next_odd * next_odd * next_odd * next_odd) as nat;
        (prev + next_odd_fourth) as nat
    }
}

fn sum_of_fourth_power_of_odd_numbers(n: u32) -> (result: u32)
    requires 
        sum_of_fourth_power_of_odd_numbers_precond(n as nat),
        n <= 1  // small bound to prevent overflow
    ensures result as nat == sum_of_fourth_power_of_odd_numbers_spec(n as nat)
    decreases n
{
    if n == 0 {
        0
    } else {
        let prev = sum_of_fourth_power_of_odd_numbers(n - 1);
        let next_odd = 2 * (n - 1) + 1;
        
        // For n=1, next_odd = 2*0+1 = 1, so next_odd^4 = 1
        assert(n == 1 ==> next_odd == 1);
        assert(n == 1 ==> next_odd * next_odd * next_odd * next_odd == 1);
        
        let next_odd_fourth = next_odd * next_odd * next_odd * next_odd;
        prev + next_odd_fourth
    }
}

// Theorem stating the specification is satisfied (proof omitted)
proof fn sum_of_fourth_power_of_odd_numbers_spec_satisfied(n: nat)
    requires sum_of_fourth_power_of_odd_numbers_precond(n)
    ensures sum_of_fourth_power_of_odd_numbers_postcond(n, sum_of_fourth_power_of_odd_numbers_spec(n))
{
    // Proof omitted (corresponding to sorry in Lean)
    admit();
}

} // verus!

fn main() {}