use vstd::prelude::*;

verus! {

spec fn fact(n: nat) -> nat 
    decreases n
{
    if n == 0 { 1 } else { n * fact((n - 1) as nat) }
}

// <vc-helpers>
proof fn fact_positive(n: nat)
    ensures fact(n) > 0
    decreases n
{
    if n == 0 {
        // fact(0) == 1 by definition, and 1 > 0
    } else {
        fact_positive((n - 1) as nat);
        // By induction hypothesis: fact((n - 1) as nat) > 0
        // fact(n) == n * fact((n - 1) as nat)
        // Since n > 0 and fact((n - 1) as nat) > 0, we have fact(n) > 0
    }
}

proof fn fact_monotonic(n: nat)
    ensures n > 0 ==> fact(n) >= n
    decreases n
{
    if n == 0 {
        // vacuously true since 0 > 0 is false
    } else if n == 1 {
        // fact(1) == 1 * fact(0) == 1 * 1 == 1, so fact(1) >= 1
    } else {
        fact_monotonic((n - 1) as nat);
        fact_positive((n - 1) as nat);
        // By induction: fact((n - 1) as nat) >= (n - 1) as nat
        // Since (n - 1) >= 1, we have fact((n - 1) as nat) >= 1
        // fact(n) == n * fact((n - 1) as nat) >= n * 1 == n
    }
}

proof fn fact_bounds(n: nat)
    requires n <= 12
    ensures fact(n) <= 479001600  // 12!
    decreases n
{
    if n == 0 {
        // fact(0) == 1 <= 479001600
    } else if n == 1 {
        // fact(1) == 1 * fact(0) == 1 * 1 == 1
    } else if n == 2 {
        // fact(2) == 2 * fact(1) == 2 * 1 == 2
        fact_bounds(1);
    } else if n == 3 {
        // fact(3) == 3 * fact(2) == 3 * 2 == 6
        fact_bounds(2);
    } else if n == 4 {
        // fact(4) == 4 * fact(3) == 4 * 6 == 24
        fact_bounds(3);
    } else if n == 5 {
        // fact(5) == 5 * fact(4) == 5 * 24 == 120
        fact_bounds(4);
    } else if n == 6 {
        // fact(6) == 6 * fact(5) == 6 * 120 == 720
        fact_bounds(5);
    } else if n == 7 {
        // fact(7) == 7 * fact(6) == 7 * 720 == 5040
        fact_bounds(6);
    } else if n == 8 {
        // fact(8) == 8 * fact(7) == 8 * 5040 == 40320
        fact_bounds(7);
    } else if n == 9 {
        // fact(9) == 9 * fact(8) == 9 * 40320 == 362880
        fact_bounds(8);
    } else if n == 10 {
        // fact(10) == 10 * fact(9) == 10 * 362880 == 3628800
        fact_bounds(9);
    } else if n == 11 {
        // fact(11) == 11 * fact(10) == 11 * 3628800 == 39916800
        fact_bounds(10);
    } else if n == 12 {
        // fact(12) == 12 * fact(11) == 12 * 39916800 == 479001600
        fact_bounds(11);
    }
}
// </vc-helpers>

// <vc-spec>
fn factorial(n: u32) -> (res: u32)
    requires n <= 12  // to prevent overflow
    ensures res == fact(n as nat)
// </vc-spec>
// <vc-code>
{
    proof {
        fact_bounds(n as nat);
    }
    
    if n == 0 {
        1
    } else {
        let mut result: u32 = 1;
        let mut i: u32 = 1;
        
        while i <= n
            invariant 
                1 <= i <= n + 1,
                result == fact((i - 1) as nat),
                i <= n + 1,
                n <= 12
            decreases n + 1 - i
        {
            proof {
                fact_bounds(i as nat);
                fact_positive((i - 1) as nat);
            }
            result = result * i;
            i = i + 1;
        }
        result
    }
}
// </vc-code>

fn main() {}

}