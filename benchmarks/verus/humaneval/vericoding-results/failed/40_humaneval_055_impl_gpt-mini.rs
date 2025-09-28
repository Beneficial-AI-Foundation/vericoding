// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n > 0
}

spec fn fib_spec(n: int) -> int
    decreases n
{
    if n <= 0 { 1 }
    else if n == 1 { 1 }
    else if n == 2 { 1 }
    else { fib_spec(n - 1) + fib_spec(n - 2) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): base cases of fib_spec */
proof fn fib_spec_base()
    ensures
        fib_spec(1 as int) == 1 as int,
        fib_spec(2 as int) == 1 as int,
    decreases 0
{
    assert(fib_spec(1 as int) == 1 as int);
    assert(fib_spec(2 as int) == 1 as int);
}

/* helper modified by LLM (iteration 5): recurrence relation for fib_spec */
proof fn fib_spec_recur(n: int)
    requires
        n >= 2 as int,
    ensures
        fib_spec(n + (1 as int)) == fib_spec(n) + fib_spec(n - (1 as int)),
    decreases n
{
    assert(n >= 2 as int);
    assert(fib_spec(n + (1 as int)) == fib_spec(n) + fib_spec(n - (1 as int)));
}

/* helper modified by LLM (iteration 5): positivity of fib_spec by induction */
proof fn fib_spec_positive(n: int)
    requires
        n >= 0 as int,
    ensures
        fib_spec(n) > 0 as int,
    decreases n
{
    if n <= 2 as int {
        proof {
            assert(fib_spec(n) == 1 as int);
            assert(fib_spec(n) > 0 as int);
        }
    } else {
        fib_spec_positive(n - (1 as int));
        fib_spec_positive(n - (2 as int));
        fib_spec_recur(n - (1 as int));
        proof {
            assert(fib_spec(n) == fib_spec(n - (1 as int)) + fib_spec(n - (2 as int)));
            assert(fib_spec(n) > 0 as int);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn fib(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures 
        result as int == fib_spec(n as int) &&
        result > 0
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): iterative fib using i64 with proofs connecting to fib_spec */
    let m: i64 = n as i64;
    if m <= 2 {
        proof {
            fib_spec_base();
            fib_spec_positive(m as int);
        }
        return 1i8;
    }

    let mut k: i64 = 2;
    let mut prev: i64 = 1;
    let mut cur: i64 = 1;

    proof {
        fib_spec_base();
    }

    while k < m
        invariant
            2 <= k && k <= m,
            (prev as int) == fib_spec((k - 1) as int),
            (cur as int) == fib_spec(k as int),
        decreases m - k
    {
        proof {
            fib_spec_recur(k as int);
            assert((prev as int) == fib_spec((k - 1) as int));
            assert((cur as int) == fib_spec(k as int));
        }
        let next = prev + cur;
        proof {
            // from fib_spec_recur and invariants, next corresponds to fib_spec(k+1)
            assert((next as int) == fib_spec((k + 1) as int));
        }
        prev = cur;
        cur = next;
        k = k + 1;
    }

    proof {
        assert(!(k < m));
        assert(k <= m);
        assert(k >= m);
        assert(k == m);
        assert((cur as int) == fib_spec(k as int));
        fib_spec_positive(m as int);
        assert((cur as int) > 0);
    }

    cur as i8
}

// </vc-code>


}

fn main() {}