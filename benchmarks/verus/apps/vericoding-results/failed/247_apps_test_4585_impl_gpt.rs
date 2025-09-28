// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int) -> bool {
    x >= 1
}

spec fn triangular_number(n: int) -> int
    recommends n >= 0
{
    n * (n + 1) / 2
}

spec fn is_minimal_time(t: int, x: int) -> bool
    recommends x >= 1
{
    t >= 1 && 
    triangular_number(t) >= x &&
    (t == 1 || triangular_number(t - 1) < x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed inner proof block; straightforward algebra to prove additive property */
proof fn lemma_triangular_additive(n: int)
    requires
        n >= 0,
    ensures
        triangular_number(n + 1) == triangular_number(n) + n + 1,
{
    assert(triangular_number(n + 1) == ((n + 1) * (n + 2)) / 2);
    assert(triangular_number(n) == (n * (n + 1)) / 2);

    assert(triangular_number(n) + n + 1 == (n * (n + 1)) / 2 + (n + 1));
    assert((n * (n + 1)) / 2 + (n + 1) == ((n * (n + 1)) + 2 * (n + 1)) / 2);

    let lhs: int = (n * (n + 1)) + 2 * (n + 1);
    let rhs: int = (n + 1) * (n + 2);
    assert(rhs == (n + 1) * n + (n + 1) * 2);
    assert((n + 1) * n == n * (n + 1));
    assert((n + 1) * 2 == 2 * (n + 1));
    assert(rhs == (n * (n + 1)) + 2 * (n + 1));
    assert(lhs == rhs);

    assert(((n * (n + 1)) + 2 * (n + 1)) / 2 == ((n + 1) * (n + 2)) / 2);
    assert(triangular_number(n) + n + 1 == triangular_number(n + 1));
}

/* helper modified by LLM (iteration 5): triangular_number(n) >= n for n >= 1 using additive lemma and non-negativity */
proof fn lemma_triangular_ge_id(n: int)
    requires
        n >= 1,
    ensures
        triangular_number(n) >= n,
{
    let m = n - 1;
    assert(m >= 0);
    lemma_triangular_additive(m);
    assert(triangular_number(n) == triangular_number(m) + n);

    assert(triangular_number(m) == (m * (m + 1)) / 2);
    assert(m >= 0);
    assert(m + 1 >= 0);
    assert(m * (m + 1) >= 0);
    assert(triangular_number(m) >= 0);

    assert(triangular_number(n) >= n);
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures is_minimal_time(result as int, x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed nested proof block in helper; keep loop invariants and arithmetic safety reasoning */
    let ghost xi: int = x as int;

    let mut t: i8 = 1;
    let mut sum: i16 = 1;

    proof {
        assert(xi >= 1);
        assert(triangular_number(1) == (1 * 2) / 2);
        assert(triangular_number(1) == 1);
        assert(triangular_number(0) == 0);
        assert(triangular_number(0) < xi);
    }

    while sum < (x as i16)
        invariant
            xi == x as int,
            (t as int) >= 1,
            (sum as int) == triangular_number(t as int),
            triangular_number((t as int) - 1) < xi,
        decreases xi - (sum as int)
    {
        let t_old: i8 = t;
        let ghost to: int = t_old as int;
        let ghost old_sum: int = sum as int;

        proof {
            assert(old_sum < xi);
            assert(xi <= 127); // i8 upper bound
            assert(to >= 1);
            lemma_triangular_ge_id(to);
            assert(triangular_number(to) >= to);
            assert(old_sum == triangular_number(to));
            assert(to <= old_sum);
            assert(old_sum <= 126); // since old_sum < xi <= 127
            assert(to <= 126);
            assert(to + 1 <= 127);
            assert(old_sum + (to + 1) <= 126 + 127);
            assert(old_sum + (to + 1) <= 253);
            assert(old_sum + (to + 1) <= 32767);
        }

        t = t + 1;

        let addend: i16 = t as i16;
        sum = sum + addend;

        proof {
            let tn: int = t as int;
            assert(tn == to + 1);
            lemma_triangular_additive(to);
            assert(triangular_number(tn) == triangular_number(to) + to + 1);
            assert(old_sum == triangular_number(to));
            assert((sum as int) == old_sum + tn);
            assert((sum as int) == triangular_number(tn));

            assert(tn - 1 == to);
            assert(triangular_number(tn - 1) == triangular_number(to));
            assert(triangular_number(tn - 1) == old_sum);
            assert(old_sum < xi);

            if (sum as int) < xi {
                assert(tn >= 2);
                assert(old_sum + tn > old_sum);
                assert((sum as int) > old_sum);
                assert(xi - (sum as int) < xi - old_sum);
            }
        }
    }

    proof {
        assert(!(sum < (x as i16)));
        assert((sum as int) >= xi);
        assert((sum as int) == triangular_number(t as int));
        assert(triangular_number(t as int) >= xi);
        assert((t as int) >= 1);
        assert(triangular_number((t as int) - 1) < xi);
        assert(is_minimal_time(t as int, xi));
    }

    t
}
// </vc-code>


}

fn main() {}