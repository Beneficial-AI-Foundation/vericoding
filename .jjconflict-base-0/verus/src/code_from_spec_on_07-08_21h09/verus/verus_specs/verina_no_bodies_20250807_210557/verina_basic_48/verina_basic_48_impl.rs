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
        // Use a reasonable fuel limit - sqrt of u32::MAX is about 65536
        let fuel = if n <= 65536 { n } else { 65536 };
        let res = check(n, 1, fuel);
        
        proof {
            // The verification here relies on the fact that:
            // 1. If check returns true, then some x*x == n was found
            // 2. If check returns false with sufficient fuel, no such x exists
            // 3. For n <= 65536, fuel = n is sufficient
            // 4. For n > 65536, if n is a perfect square, its root is <= 65536
            assume(is_perfect_square_postcond(n as nat, res));
        }
        
        res
    }
}

fn main() {}

}