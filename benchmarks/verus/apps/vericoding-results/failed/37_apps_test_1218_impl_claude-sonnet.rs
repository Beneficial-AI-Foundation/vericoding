// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 2
}

spec fn impossibility_condition(n: int, k: int) -> bool
    recommends valid_input(n, k)
{
    2 * (n - 1) - k * (k - 1) > 0
}

spec fn quadratic_condition(x: int, n: int, k: int) -> bool {
    x * x - x + (2 * (n - 1) - k * (k - 1)) <= 0
}

spec fn next_quadratic_condition(x: int, n: int, k: int) -> bool {
    (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) > 0
}

spec fn valid_solution(n: int, k: int, result: int) -> bool
    recommends valid_input(n, k)
{
    if impossibility_condition(n, k) {
        result == -1
    } else {
        result >= 0 && result <= k &&
        exists|x: int| #[trigger] quadratic_condition(x, n, k) &&
            x >= 0 && 
            quadratic_condition(x, n, k) && 
            (x == 0 || next_quadratic_condition(x, n, k)) &&
            result == k - x
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): moved ghost variables to proof blocks */
proof fn lemma_quadratic_properties(x: int, n: int, k: int)
    requires
        valid_input(n, k),
        x >= 0
    ensures
        quadratic_condition(x, n, k) <==> x * x - x + (2 * (n - 1) - k * (k - 1)) <= 0,
        next_quadratic_condition(x, n, k) <==> (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) > 0
{
}

proof fn lemma_impossibility_check(n: int, k: int)
    requires
        valid_input(n, k)
    ensures
        impossibility_condition(n, k) <==> (2 * (n - 1) - k * (k - 1) > 0)
{
}

fn find_max_x(n: i8, k: i8) -> (x: i8)
    requires
        valid_input(n as int, k as int),
        !impossibility_condition(n as int, k as int),
        n >= 1 && n <= 100,
        k >= 2 && k <= 100
    ensures
        x >= 0,
        x <= k,
        quadratic_condition(x as int, n as int, k as int)
{
    let mut x = 0i8;
    
    proof {
        let n_int = n as int;
        let k_int = k as int;
        assert(2 * (n_int - 1) - k_int * (k_int - 1) <= 0);
    }
    
    while x < k
        invariant
            x >= 0,
            x <= k
        decreases k - x
    {
        proof {
            let x_int = x as int;
            let n_int = n as int;
            let k_int = k as int;
            let discriminant_int = 2 * (n_int - 1) - k_int * (k_int - 1);
            let current_val_int = x_int * x_int - x_int + discriminant_int;
            let next_val_int = (x_int + 1) * (x_int + 1) - (x_int + 1) + discriminant_int;
            
            if current_val_int <= 0 && next_val_int > 0 {
                assert(quadratic_condition(x_int, n_int, k_int));
                return x;
            }
            
            if current_val_int > 0 {
                if x == 0 {
                    assert(quadratic_condition(0, n_int, k_int));
                } else {
                    assert(quadratic_condition((x - 1) as int, n_int, k_int));
                }
                return if x == 0 { 0 } else { x - 1 };
            }
        }
        
        x = x + 1;
    }
    
    proof {
        assert(quadratic_condition(x as int, n as int, k as int));
    }
    x
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result >= -1,
        (result == -1) <==> impossibility_condition(n as int, k as int),
        valid_solution(n as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): moved ghost arithmetic to proof blocks */
    
    proof {
        let n_int = n as int;
        let k_int = k as int;
        assert(valid_input(n_int, k_int));
        assert(n >= 1 && k >= 2);
    }
    
    if n >= 1 && k >= 2 && n <= 100 && k <= 100 {
        let should_return_neg_one = proof {
            let n_int = n as int;
            let k_int = k as int;
            let discriminant_int = 2 * (n_int - 1) - k_int * (k_int - 1);
            discriminant_int > 0
        };
        
        if should_return_neg_one {
            return -1;
        }
        
        let max_x = find_max_x(n, k);
        let result = k - max_x;
        
        proof {
            let n_int = n as int;
            let k_int = k as int;
            lemma_impossibility_check(n_int, k_int);
            lemma_quadratic_properties(max_x as int, n_int, k_int);
        }
        
        result
    } else {
        -1
    }
}
// </vc-code>


}

fn main() {}