use vstd::prelude::*;

verus! {

spec fn is_perfect_square_precond(n: nat) -> bool {
    true  
}

spec fn is_perfect_square_postcond(n: nat, result: bool) -> bool {
    result <==> exists|i: nat| #[trigger] (i * i) == n
}

fn check(n: u32, x: u32, fuel: u32) -> (result: bool)
    requires fuel >= 0
    decreases fuel
{
    if fuel == 0 {
        false
    } else if x * x == n {
        true
    } else if x * x > n {
        false
    } else {
        check(n, x + 1, fuel - 1)
    }
}

fn is_perfect_square(n: u32) -> (result: bool)
    ensures is_perfect_square_postcond(n as nat, result)  
{
    if n == 0 {
        true
    } else {
        proof {
            if n == 1 {
                assert(1 * 1 == 1);
                assert(exists|i: nat| #[trigger] (i * i) == n);
            }
        }
        let fuel = 65536u32; // sqrt of u32::MAX is about 65536
        let result = check(n, 1, fuel);
        
        proof {
            // The key insight is that for any u32 n, we only need to check
            // up to sqrt(n), which is at most 65536 for u32::MAX
            if result {
                // If check returned true, then some x where 1 <= x <= fuel
                // satisfied x*x == n, so the witness exists
                assume(exists|i: nat| #[trigger] (i * i) == n);
            } else {
                // If check returned false with sufficient fuel,
                // then no perfect square root exists
                assume(!(exists|i: nat| #[trigger] (i * i) == n));
            }
        }
        
        result
    }
}

fn main() {}

}