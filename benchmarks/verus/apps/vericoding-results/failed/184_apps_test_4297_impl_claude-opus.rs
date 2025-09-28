// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn divisible_by_both(result: int, n: int) -> bool
    recommends n >= 1
{
    result % 2 == 0 && result % n == 0
}

spec fn is_smallest(result: int, n: int) -> bool
    recommends n >= 1
{
    forall|k: int| 1 <= k < result ==> !(#[trigger] (k % 2) == 0 && #[trigger] (k % n) == 0)
}

spec fn lcm(a: int, b: int) -> int
    recommends a >= 1 && b >= 1
{
    if a % b == 0 {
        a
    } else if b % a == 0 {
        b
    } else {
        a * b
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added lemma to prove n*2 is smallest when n is odd */
proof fn lemma_smallest_divisible_odd(n: int)
    requires
        n >= 1,
        n % 2 != 0,
    ensures
        forall|k: int| 1 <= k < n * 2 ==> !(k % 2 == 0 && k % n == 0),
{
    assert forall|k: int| 1 <= k < n * 2 implies !(k % 2 == 0 && k % n == 0) by {
        if k % 2 == 0 && k % n == 0 {
            // k is even and divisible by n
            // Since n is odd and k is divisible by n, k must be at least n
            assert(k >= n);
            // Since k is even and less than n*2, k could be n (but n is odd, contradiction)
            // or k >= 2*n (but then k >= n*2, contradiction with k < n*2)
            if k == n {
                assert(n % 2 == 0);  // Contradiction since n is odd
                assert(false);
            } else {
                assert(k >= 2 * n);  // Since k is divisible by n and k > n
                assert(false);  // Contradiction with k < n * 2
            }
        }
    }
}

proof fn lemma_smallest_divisible_even(n: int)
    requires
        n >= 1,
        n % 2 == 0,
    ensures
        forall|k: int| 1 <= k < n ==> !(k % 2 == 0 && k % n == 0),
{
    assert forall|k: int| 1 <= k < n implies !(k % 2 == 0 && k % n == 0) by {
        if k % n == 0 && 1 <= k < n {
            assert(false);  // No positive k < n can be divisible by n
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires 
        n >= 1,
    ensures 
        result >= 1,
        result as int % 2 == 0 && result as int % n as int == 0,
        forall|k: int| 1 <= k < result as int ==> !(#[trigger] (k % 2) == 0 && #[trigger] (k % n as int) == 0),
        (n as int % 2 == 0 ==> result as int == n as int) && (n as int % 2 != 0 ==> result as int == n as int * 2),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added overflow check and proper proofs for smallest value */
    if n % 2 == 0 {
        proof {
            lemma_smallest_divisible_even(n as int);
        }
        n
    } else {
        // Check for overflow before multiplication
        assert(n <= 63) by {
            assert(n <= 127);  // i8 max value
            assert(n * 2 <= 126);  // Would fit in i8
        }
        let result: i8 = n * 2;
        
        proof {
            assert(result as int == n as int * 2);
            assert(result as int % 2 == 0);
            assert(result as int % n as int == 0);
            lemma_smallest_divisible_odd(n as int);
        }
        
        result
    }
}
// </vc-code>


}

fn main() {}