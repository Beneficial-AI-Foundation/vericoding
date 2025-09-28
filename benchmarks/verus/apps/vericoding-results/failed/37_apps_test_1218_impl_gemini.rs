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
#[verifier(spinoff_prover)]
proof fn lemma_parabola_monotonic(i: int, j: int, C: int)
    requires
        1 <= j <= i,
    ensures
        (j * j - j + C) <= (i * i - i + C),
    decreases i - j
{
    if i > j {
        lemma_parabola_monotonic(i - 1, j, C);
    }
}

proof fn lemma_quadratic_range(y: int, n: int, k: int)
    requires
        y >= 0,
        !impossibility_condition(n, k),
        quadratic_condition(y, n, k),
    ensures
        forall|j: int| 0 <= j <= y ==> quadratic_condition(j, n, k),
{
    let C = 2 * (n - 1) - k * (k - 1);
    let f = |i: int| i * i - i + C;
    forall|j: int| 0 <= j <= y implies quadratic_condition(j, n, k) by {
        if j == 0 {
            assert(C <= 0);
            assert(f(0) <= 0);
        } else {
            lemma_parabola_monotonic(y, j, C);
            assert(f(j) <= f(y));
            assert(f(y) <= 0);
            assert(f(j) <= 0);
        }
    }
}

proof fn lemma_next_quadratic_at_k(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        next_quadratic_condition(k, n, k),
{
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
    let n_int = n as int;
    let k_int = k as int;

    let C = 2 * (n_int - 1) - k_int * (k_int - 1);

    if C > 0 {
        assert(impossibility_condition(n_int, k_int));
        return -1;
    }
    
    assert(!impossibility_condition(n_int, k_int));

    let mut x: int = 0;
    while x < k_int && quadratic_condition(x + 1, n_int, k_int)
        invariant
            valid_input(n_int, k_int),
            !impossibility_condition(n_int, k_int),
            x >= 0,
            x <= k_int,
            forall|j: int| 0 <= j <= x ==> quadratic_condition(j, n_int, k_int),
        decreases k_int - x
    {
        proof {
            lemma_quadratic_range(x + 1, n_int, k_int);
        }
        x = x + 1;
    }

    proof {
        if x < k_int {
            assert(next_quadratic_condition(x, n_int, k_int));
        } else {
            assert(x == k_int);
            lemma_next_quadratic_at_k(n_int, k_int);
            assert(next_quadratic_condition(x, n_int, k_int));
        }
    }
    
    let result = k_int - x;

    assert(x >= 0);
    assert(quadratic_condition(x, n_int, k_int));
    assert(x == 0 || next_quadratic_condition(x, n_int, k_int));
    assert(exists|x_found: int| 
        #[trigger] quadratic_condition(x_found, n_int, k_int) &&
        x_found >= 0 && 
        (x_found == 0 || next_quadratic_condition(x_found, n_int, k_int)) &&
        result == k_int - x_found);

    assert(valid_solution(n_int, k_int, result));

    return (k_int - x) as i8;
}
// </vc-code>


}

fn main() {}