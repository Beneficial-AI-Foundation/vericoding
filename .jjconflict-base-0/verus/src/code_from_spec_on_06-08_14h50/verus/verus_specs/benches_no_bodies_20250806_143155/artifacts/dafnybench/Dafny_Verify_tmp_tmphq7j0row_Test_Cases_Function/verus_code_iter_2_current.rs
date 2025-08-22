use vstd::prelude::*;

verus! {
    spec fn average(a: int, b: int) -> int {
        (a + b) / 2
    }

    proof fn triple_conditions(x: int) -> (r: int)
        ensures r == 3 * x
    {   
        /* code modified by LLM (iteration 1): Fixed function body to properly return the value */
        3 * x
    }

    proof fn triple_prime(x: int) -> (r: int) 
        ensures 
            average(r, 3 * x) == 3 * x,
            r == 3 * x
    {
        /* code modified by LLM (iteration 1): Added proof block with assertions to verify the ensures clauses */
        proof {
            let r = 3 * x;
            assert(r == 3 * x);
            assert(average(r, 3 * x) == average(3 * x, 3 * x));
            assert(average(3 * x, 3 * x) == (3 * x + 3 * x) / 2);
            assert((3 * x + 3 * x) / 2 == (6 * x) / 2);
            assert((6 * x) / 2 == 3 * x);
        }
        3 * x
    }

    proof fn prove_specifications_equivalent(x: int) {
        /* code modified by LLM (iteration 1): Updated to use function calls correctly and added proof block */
        proof {
            let result1 = triple_conditions(x);
            let result2 = triple_prime(x);
            
            assert(result1 == 3 * x);
            assert(result2 == 3 * x);
            assert(result1 == result2);
        }
    }
}

fn main() {}