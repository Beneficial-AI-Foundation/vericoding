use vstd::prelude::*;

verus! {
    spec fn average(a: int, b: int) -> int {
        (a + b) / 2
    }

    proof fn triple_conditions(x: int) -> (r: int)
        ensures r == 3 * x
    {   
        let r = 3 * x;
        assert(r == 3 * x);
        r
    }

    proof fn triple_prime(x: int) -> (r: int) 
        ensures 
            average(r, 3 * x) == 3 * x,
            r == 3 * x
    {
        let r = 3 * x;
        r
    }

    proof fn prove_specifications_equivalent(x: int) {
        let result1 = triple_conditions(x);
        let result2 = triple_prime(x);
        
        assert(result1 == result2);
    }
}

fn main() {}