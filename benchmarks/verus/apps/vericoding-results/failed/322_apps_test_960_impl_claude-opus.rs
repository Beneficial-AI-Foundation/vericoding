// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 2
}

spec fn satisfies_constraint(x: int, n: int, k: int) -> bool {
    x > 0 && k > 0 && (x / k) * (x % k) == n
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_unique_solution(n: int, k: int, q: int, r: int)
    requires
        n >= 1,
        k >= 2,
        0 <= r,
        r < k,
        q * r == n
    ensures
        satisfies_constraint(q * k + r, n, k),
        forall|x: int| satisfies_constraint(x, n, k) ==> q * k + r <= x
{
    let x_min = q * k + r;
    assert(x_min > 0) by {
        assert(q >= 1) by {
            if q <= 0 {
                assert(q * r <= 0);
                assert(n >= 1);
                assert(false);
            }
        }
        assert(x_min >= k);
    }
    assert(x_min / k == q);
    assert(x_min % k == r);
    assert((x_min / k) * (x_min % k) == q * r);
    assert(satisfies_constraint(x_min, n, k));
    
    assert forall|x: int| satisfies_constraint(x, n, k) implies x_min <= x by {
        let x_q = x / k;
        let x_r = x % k;
        assert(x_q * x_r == n);
        assert(0 <= x_r < k);
        
        if x_r == 0 {
            assert(x_q * 0 == n);
            assert(false);
        }
        
        assert(x_r >= 1);
        assert(x_q >= n / x_r);
        
        if x_r > r {
            assert(x_q >= n / x_r);
            assert(n / x_r <= n / (r + 1));
            assert(x_q * k >= q * k);
            assert(x >= x_q * k + x_r);
            assert(x >= q * k + r + 1);
            assert(x > x_min);
        } else if x_r < r {
            assert(x_q > n / x_r);
            assert(x_q > q);
            assert(x_q >= q + 1);
            assert(x >= (q + 1) * k);
            assert(x >= q * k + k);
            assert(x > q * k + r);
            assert(x > x_min);
        } else {
            assert(x_r == r);
            assert(x_q * r == n);
            assert(q * r == n);
            assert(x_q == q);
            assert(x == x_q * k + x_r);
            assert(x == q * k + r);
            assert(x == x_min);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result > 0,
        satisfies_constraint(result as int, n as int, k as int),
        forall|x: int| #[trigger] satisfies_constraint(x, n as int, k as int) ==> result as int <= x
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed trigger annotation in assert statement */
    let mut r: i8 = 1;
    
    while r < k
        invariant
            1 <= r,
            r <= k,
            forall|i: int| 1 <= i && i < r ==> #[trigger] ((n as int) % i) != 0
        decreases k - r
    {
        if n % r == 0 {
            let q = n / r;
            let result = q * k + r;
            
            proof {
                lemma_unique_solution(n as int, k as int, q as int, r as int);
            }
            
            return result;
        }
        r = r + 1;
    }
    
    assert(false) by {
        assert(forall|i: int| 1 <= i && i < k ==> #[trigger] ((n as int) % i) != 0);
        assert((n as int) % 1 == 0);
    }
    unreached()
}
// </vc-code>


}

fn main() {}