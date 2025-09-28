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
/* helper modified by LLM (iteration 5): proved division decomposition for q*k + r */
proof fn div_decomp(q: int, r: int, k: int)
    requires
        k > 0,
        0 <= r,
        r < k,
    ensures
        (q * k + r) / k == q,
        (q * k + r) % k == r,
{
    assert((q * k + r) / k == q + r / k);
    assert(r / k == 0);
    assert(q + 0 == q);
    assert((q * k + r) % k == r % k);
    assert(r % k == r);
}

/* helper modified by LLM (iteration 5): if n divisible by r and both >=1 then quotient >=1 */
proof fn div_ge_one(n: int, r: int)
    requires
        n >= 1,
        r >= 1,
        n % r == 0,
    ensures
        n / r >= 1,
{
    let q = n / r;
    assert(n == q * r + n % r);
    assert(n % r == 0);
    assert(n == q * r);
    if q <= 0 {
        assert(q * r <= 0);
        assert(n <= 0);
    }
    assert(q >= 1);
}

/* helper modified by LLM (iteration 5): construct x = (n/r)*k + r as a valid solution */
proof fn construct_solution(n: int, k: int, r: int) -> (result: int)
    requires
        n >= 1,
        k >= 2,
        1 <= r,
        r < k,
        n % r == 0,
    ensures
        result > 0,
        satisfies_constraint(result, n, k),
{
    let q = n / r;
    let x = q * k + r;
    div_decomp(q, r, k);
    div_ge_one(n, r);
    assert(q >= 1);
    assert(x > 0);
    assert((x / k) == q);
    assert((x % k) == r);
    assert((x / k) * (x % k) == q * r);
    assert(q * r == n);
    let result: int = x;
    result
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
    /* code modified by LLM (iteration 5): implement search using i8 and parenthesized casts to avoid parsing issues */
    let mut r: i8 = 2;
    let mut best_r: i8 = 1;
    let mut best_q: i8 = n / 1;
    let mut best_x: i8 = best_q * k + best_r;

    while r < k
        invariant
            1 <= (r as int),
            (r as int) <= (k as int),
            1 <= (best_r as int),
            (best_r as int) < (r as int),
            (n as int) % (best_r as int) == 0,
            (best_x as int) == (n as int / (best_r as int)) * (k as int) + (best_r as int),
            forall|d: int| 1 <= d && d < (r as int) && (n as int) % d == 0 ==> (best_x as int) <= (n as int / d) * (k as int) + d,
        decreases (k as int) - (r as int)
    {
        if n % r == 0 {
            let q = n / r;
            let cand = q * k + r;
            if cand < best_x {
                best_x = cand;
                best_r = r;
                best_q = q;
            }
        }
        r = r + 1;
    }

    proof {
        assert(1 <= (best_r as int));
        assert((best_r as int) < (k as int));
        assert((n as int) % (best_r as int) == 0);

        let bq: int = best_q as int;
        let br: int = best_r as int;
        assert(bq == (n as int) / br);
        assert((best_x as int) == bq * (k as int) + br);

        div_decomp(bq, br, k as int);
        assert(((best_x as int) / (k as int)) == bq);
        assert(((best_x as int) % (k as int)) == br);
        assert(((best_x as int) / (k as int)) * ((best_x as int) % (k as int)) == bq * br);
        assert(bq * br == (n as int));

        assert(forall|d: int| 1 <= d && d < (k as int) && (n as int) % d == 0 ==> (best_x as int) <= (n as int / d) * (k as int) + d);
    }

    best_x as i8
}
// </vc-code>


}

fn main() {}