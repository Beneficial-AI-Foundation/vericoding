// <vc-preamble>
use vstd::prelude::*;

verus! {

    spec fn valid_input(n: int) -> bool {
        1 <= n <= 1000
    }
    
    spec fn max_groups_with_at_least_three(n: int) -> int
        recommends valid_input(n)
    {
        n / 3
    }
    
    spec fn valid_solution(n: int, result: int) -> bool
        recommends valid_input(n)
    {
        result == max_groups_with_at_least_three(n) &&
        result >= 0 &&
        result <= n
    }

    fn solve_groups(n: i8) -> (result: i8)
        requires valid_input(n as int)
        ensures valid_solution(n as int, result as int)
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
// </vc-spec>
// <vc-code>
{
        let result = n / 3;
        
        assert(result == max_groups_with_at_least_three(n as int));
        assert(result >= 0) by {
            if (n < 0) { // Should not happen given valid_input(n) implies n >= 1
            } else {
                assert(n / 3 >= 0);
            }
        }
        assert(result <= n) by {
            // Proof that n / 3 <= n for n >= 1
            if (n >= 1) {
                // Case 1: n >= 3
                // If n >= 3, then n/3 multiplied by 3 is (n/3)*3, which is <= n
                // n/3 <= n/3 * 3 / 3, and n/3 * 3 <= n
                // Let k = n / 3. Then 3*k <= n. We want to show k <= n.
                // Since n >= 1, we know k >= 0. k * 3 >= k. So 3*k >= k.
                // Thus, n >= 3*k >= k.
            } else if (n >=1 && n < 3) { // n can be 1 or 2
                // If n = 1, then n/3 = 0. 0 <= 1.
                // If n = 2, then n/3 = 0. 0 <= 2.
            }
        }

        result
    }
// </vc-code>


}

fn main() {}