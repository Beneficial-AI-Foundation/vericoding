// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 0 && k >= 0 && k + 1 > 0
}

spec fn valid_output(result: Seq<int>, n: int, k: int) -> bool {
    result.len() == 3 &&
    result[0] >= 0 && result[1] >= 0 && result[2] >= 0 &&
    result[1] == result[0] * k &&
    result[0] + result[1] <= n / 2 &&
    result[2] == n - result[0] - result[1]
}

spec fn optimal_diplomas(n: int, k: int) -> int
    recommends valid_input(n, k)
{
    (n / 2) / (k + 1)
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_division_le_and_nonneg(t: int, d: int)
    requires
        t >= 0,
        d > 0,
    ensures
        (t / d) * d <= t,
        0 <= t / d,
{
    assert(t == (t / d) * d + (t % d));
    assert(0 <= t % d);
    assert((t / d) * d <= (t / d) * d + (t % d));
    assert(0 <= t / d);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: Vec<i8>)
    requires valid_input(n as int, k as int)
    ensures 
        valid_output(result@.map(|i, x| x as int), n as int, k as int) &&
        result@[0] as int == optimal_diplomas(n as int, k as int)
// </vc-spec>
// <vc-code>
{
    let n_int: int = n as int;
    let k_int: int = k as int;

    let denom: int = k_int + 1;
    let half_n: int = n_int / 2;

    proof {
        assert(n_int >= 0);
        assert(k_int >= 0);
        assert(denom > 0);
    }

    let x: int = half_n / denom;
    let r0_i: int = x;
    let r1_i: int = x * k_int;

    lemma_division_le_and_nonneg(half_n, denom);

    proof {
        assert(x == half_n / denom);
        assert(x * denom <= half_n);
        assert(0 <= x);
        assert(0 <= r1_i);
        assert(k_int <= denom);
        assert(x * k_int <= x * denom);
        assert(r1_i <= half_n);
        assert(r0_i + r1_i == x * (k_int + 1));
        assert(r0_i + r1_i <= half_n);
        // Show half_n >= 0
        assert(half_n >= 0);
    }

    let r2_i: int = n_int - r0_i - r1_i;

    proof {
        // r2_i >= 0 since r0_i + r1_i <= half_n and n_int - half_n >= 0
        assert(n_int == (n_int / 2) * 2 + (n_int % 2));
        assert(0 <= n_int % 2);
        assert(0 <= n_int / 2);
        assert(n_int - (n_int / 2) == (n_int / 2) + (n_int % 2));
        assert(n_int - (n_int / 2) >= 0);
        assert(r2_i >= n_int - half_n);
        assert(r2_i >= 0);
    }

    // Bounds to allow casts to i8
    proof {
        assert(n_int <= i8::MAX as int);
        assert(r0_i <= half_n);
        assert(r1_i <= half_n);
        assert(half_n <= n_int);
        assert(0 <= r0_i && r0_i <= 127);
        assert(0 <= r1_i && r1_i <= 127);
        assert(r2_i <= n_int);
        assert(0 <= r2_i && r2_i <= 127);
    }

    let mut res: Vec<i8> = Vec::new();
    res.push(r0_i as i8);
    res.push(r1_i as i8);
    res.push(r2_i as i8);

    proof {
        assert(res@.len() == 3);
        assert(res@[0] as int == r0_i);
        assert(res@[1] as int == r1_i);
        assert(res@[2] as int == r2_i);
        assert(res@[1] as int == res@[0] as int * k_int);
        assert(res@[0] as int + res@[1] as int <= n_int / 2);
        assert(res@[2] as int == n_int - res@[0] as int - res@[1] as int);
        assert(res@[0] as int == (n_int / 2) / (k_int + 1));
        assert(res@[0] as int == optimal_diplomas(n_int, k_int));
    }

    res
}
// </vc-code>


}

fn main() {}