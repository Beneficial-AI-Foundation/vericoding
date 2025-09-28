// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int) -> bool {
    n > 0 && n <= 10000 && m > 1 && m <= 10
}

spec fn min_moves(n: int) -> int
    recommends n > 0
{
    if n % 2 == 0 { n / 2 } else { n / 2 + 1 }
}

spec fn valid_move_count(n: int, k: int) -> bool
    recommends n > 0
{
    min_moves(n) <= k <= n
}

spec fn is_valid_solution(n: int, m: int, result: int) -> bool
    recommends valid_input(n, m)
{
    result == -1 || (result > 0 && result % m == 0 && valid_move_count(n, result))
}

spec fn no_smaller_solution(n: int, m: int, result: int) -> bool
    recommends valid_input(n, m)
{
    result == -1 ==> forall|k: int| min_moves(n) <= k <= n ==> #[trigger] (k % m) != 0
}

spec fn is_minimal_solution(n: int, m: int, result: int) -> bool
    recommends valid_input(n, m)
{
    result != -1 ==> forall|k: int| (min_moves(n) <= k <= n && k < result) ==> #[trigger] (k % m) != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
    requires 
        valid_input(n as int, m as int)
    ensures 
        is_valid_solution(n as int, m as int, result as int) &&
        no_smaller_solution(n as int, m as int, result as int) &&
        is_minimal_solution(n as int, m as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop invariant and overflow issues */
    // We know n > 0 from requires clause
    let min_k: i8 = if n % 2 == 0 { n / 2 } else { n / 2 + 1 };
    let mut k: i8 = min_k;
    
    proof {
        // Establish that n > 0 for min_moves calls
        assert(valid_input(n as int, m as int));
        assert(n as int > 0);
        assert(n as int <= 10000);
        assert(m as int > 1);
        assert(min_k as int == min_moves(n as int));
    }
    
    while k <= n
        invariant
            valid_input(n as int, m as int),
            min_k as int == min_moves(n as int),
            min_k as int <= k as int <= n as int + 1,
            forall|j: int| (min_moves(n as int) <= j && j < k as int) ==> #[trigger] (j % (m as int)) != 0,
        decreases n as int - k as int + 1
    {
        proof {
            assert(m as int > 1);
            assert(m as int != 0);
            assert(k as int <= n as int);
        }
        
        if k % m == 0 {
            proof {
                assert(k as int % m as int == 0);
                assert(min_moves(n as int) <= k as int);
                assert(k as int <= n as int);
                assert(valid_move_count(n as int, k as int));
                assert(is_valid_solution(n as int, m as int, k as int));
                assert(forall|j: int| (min_moves(n as int) <= j && j < k as int) ==> #[trigger] (j % (m as int)) != 0);
                assert(is_minimal_solution(n as int, m as int, k as int));
            }
            return k;
        }
        
        proof {
            assert(k as int < n as int + 1);
            assert(k as int + 1 <= n as int + 1);
            assert(n as int <= 10000);
            assert(k as int <= 10000);
            assert(k as int + 1 <= 10001);
            assert(k as int + 1 <= i8::MAX);
        }
        
        k = k + 1;
    }
    
    proof {
        assert(k as int > n as int);
        assert(forall|j: int| (min_moves(n as int) <= j && j <= n as int) ==> #[trigger] (j % (m as int)) != 0);
        assert(no_smaller_solution(n as int, m as int, -1));
        assert(is_valid_solution(n as int, m as int, -1));
        assert(is_minimal_solution(n as int, m as int, -1));
    }
    -1
}
// </vc-code>


}

fn main() {}