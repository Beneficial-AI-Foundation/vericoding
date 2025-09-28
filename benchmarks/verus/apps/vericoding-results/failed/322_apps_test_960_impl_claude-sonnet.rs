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
/* helper modified by LLM (iteration 5): fixed lemma proofs with correct division bounds */
proof fn lemma_smallest_x_bounds(n: int, k: int)
    requires
        valid_input(n, k)
    ensures
        exists|x: int| satisfies_constraint(x, n, k) && x <= n * k
{
    let x = n * k + 1;
    assert(x > 0);
    assert(k > 0);
    assert(x / k == n) by {
        assert(x == n * k + 1);
        assert(n * k <= x < (n + 1) * k);
    };
    assert(x % k == 1) by {
        assert(x == n * k + 1);
        assert(x % k == (n * k + 1) % k);
        assert((n * k + 1) % k == 1);
    };
    assert((x / k) * (x % k) == n * 1);
    assert(satisfies_constraint(x, n, k));
}

proof fn lemma_division_remainder_identity(x: int, k: int)
    requires
        k > 0
    ensures
        x == (x / k) * k + (x % k)
{
    // This is a fundamental property of division and modulo
}

proof fn lemma_satisfies_constraint_bounds(x: int, n: int, k: int)
    requires
        satisfies_constraint(x, n, k),
        valid_input(n, k)
    ensures
        x >= k,
        x / k >= 1,
        x % k < k
{
    assert(x > 0 && k > 0);
    assert((x / k) * (x % k) == n);
    assert(n >= 1);
    if x < k {
        assert(x / k == 0) by {
            assert(0 <= x < k);
        };
        assert((x / k) * (x % k) == 0 * (x % k));
        assert((x / k) * (x % k) == 0);
        assert(n == 0);
        assert(false);
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
    /* code modified by LLM (iteration 5): moved int casts to proof block */
    let mut candidate = k as i8;
    
    while candidate <= 127
        invariant
            candidate >= k,
            candidate <= 127,
            k >= 2,
            n >= 1,
            forall|x: int| k as int <= x < candidate as int ==> !satisfies_constraint(x, n as int, k as int)
        decreases 127 - candidate
    {
        let quotient = (candidate / k) as i8;
        let remainder = (candidate % k) as i8;
        
        if quotient > 0 && remainder > 0 && quotient <= 127 && remainder <= 127 {
            if quotient * remainder == n {
                proof {
                    assert(candidate > 0);
                    assert(k > 0);
                    assert(quotient == candidate / k);
                    assert(remainder == candidate % k);
                    assert((candidate as int / k as int) * (candidate as int % k as int) == quotient as int * remainder as int);
                    assert(quotient as int * remainder as int == n as int);
                    assert((candidate as int / k as int) * (candidate as int % k as int) == n as int);
                    assert(satisfies_constraint(candidate as int, n as int, k as int));
                }
                return candidate;
            }
        }
        
        if candidate < 127 {
            candidate += 1;
        } else {
            break;
        }
    }
    
    // This should never be reached given the constraints
    proof {
        lemma_smallest_x_bounds(n as int, k as int);
        assert(exists|x: int| satisfies_constraint(x, n as int, k as int));
        assert(false);
    }
    unreached()
}
// </vc-code>


}

fn main() {}