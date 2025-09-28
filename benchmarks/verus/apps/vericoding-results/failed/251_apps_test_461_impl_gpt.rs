// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int, c: int) -> bool {
    1 <= n <= 100 && 1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

spec fn min_distance(n: int, a: int, b: int, c: int) -> int
    recommends valid_input(n, a, b, c)
{
    if n == 1 { 0 } else { (n - 1) * min(a, b) }
}

spec fn min(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

spec fn max(x: int, y: int) -> int {
    if x >= y { x } else { y }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): strengthen and simplify max/min reasoning; add left-side monotonicity for multiplication */
proof fn lemma_le_max_left(x: int, y: int)
    ensures
        x <= max(x, y),
{
    if x >= y {
        assert(max(x, y) == x);
    } else {
        assert(max(x, y) == y);
        assert(x <= y);
    }
}

proof fn lemma_le_max_right(x: int, y: int)
    ensures
        y <= max(x, y),
{
    if x >= y {
        assert(max(x, y) == x);
        assert(y <= x);
    } else {
        assert(max(x, y) == y);
    }
}

/* helper modified by LLM (iteration 3): direct proof that min(a,b) <= max(a, max(b,c)) */
proof fn lemma_min_le_max(a: int, b: int, c: int)
    ensures
        min(a, b) <= max(a, max(b, c)),
{
    if a <= b {
        assert(min(a, b) == a);
        lemma_le_max_left(a, max(b, c));
    } else {
        assert(min(a, b) == b);
        // b <= max(b,c)
        lemma_le_max_left(b, c);
        // max(b,c) <= max(a, max(b,c))
        lemma_le_max_right(a, max(b, c));
        proof {
            assert(b <= max(b, c));
            assert(max(b, c) <= max(a, max(b, c)));
            assert(b <= max(a, max(b, c)));
        }
    }
}

proof fn lemma_exec_min_eq_spec(a: i8, b: i8)
    ensures
        (if a <= b { a } else { b }) as int == min(a as int, b as int),
{
    if a <= b {
        assert(min(a as int, b as int) == a as int);
    } else {
        assert(min(a as int, b as int) == b as int);
    }
}

/* helper modified by LLM (iteration 3): multiplication monotonicity in the right argument for nonnegative multiplier */
proof fn lemma_mul_mono_nonneg(k: int, x: int, y: int)
    requires
        0 <= k,
        x <= y,
    ensures
        k * x <= k * y,
{
}

/* helper modified by LLM (iteration 3): multiplication monotonicity in the left argument for nonnegative multiplicand */
proof fn lemma_mul_mono_nonneg_left(k1: int, k2: int, x: int)
    requires
        0 <= x,
        k1 <= k2,
    ensures
        k1 * x <= k2 * x,
{
}

proof fn lemma_min_lower_bound(a: int, b: int, lb: int)
    requires
        lb <= a,
        lb <= b,
    ensures
        lb <= min(a, b),
{
    if a <= b {
        assert(min(a, b) == a);
        assert(lb <= min(a, b));
    } else {
        assert(min(a, b) == b);
        assert(lb <= min(a, b));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, c: i8) -> (result: i8)
    requires 
        valid_input(n as int, a as int, b as int, c as int)
    ensures 
        result >= 0,
        n == 1 ==> result == 0,
        result as int <= (n as int - 1) * max(a as int, max(b as int, c as int)),
        result as int == min_distance(n as int, a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): avoid exec 'int' locals; compute with i16, use ghost ints for proofs */
    if n == 1 {
        proof {
            assert(min_distance(n as int, a as int, b as int, c as int) == 0);
        }
        0
    } else {
        let m8: i8 = if a <= b { a } else { b };
        let k16: i16 = (n as i16) - 1;
        let m16: i16 = m8 as i16;
        // Prove i16 multiplication does not overflow and relate to specs
        proof {
            lemma_exec_min_eq_spec(a, b);
            let ghost m_g: int = min(a as int, b as int);
            let ghost k_g: int = n as int - 1;
            let ghost r_g: int = k_g * m_g;

            // From requires: 1 <= n <= 100, 1 <= a,b <= 100
            assert(1 <= n as int);
            assert(n as int <= 100);
            assert(1 <= a as int);
            assert(a as int <= 100);
            assert(1 <= b as int);
            assert(b as int <= 100);

            // Basic properties
            assert(k_g >= 0);
            assert(k_g <= 99);
            lemma_min_lower_bound(a as int, b as int, 1);
            assert(m_g >= 1);
            assert(m_g <= 100);

            // Bound product: k_g * m_g <= 99 * 100 = 9900
            lemma_mul_mono_nonneg_left(k_g, 99, m_g);
            lemma_mul_mono_nonneg(99, m_g, 100);
            assert(r_g <= 99 * 100);
            assert(r_g <= 9900);
            assert(0 <= r_g);

            // Upper-bound obligation used elsewhere
            lemma_min_le_max(a as int, b as int, c as int);
            lemma_mul_mono_nonneg(k_g, m_g, max(a as int, max(b as int, c as int)));
            assert(min_distance(n as int, a as int, b as int, c as int) == r_g);
        }
        let r16: i16 = k16 * m16; // safe: 0 <= (n-1)*min(a,b) <= 9900 < i16::MAX
        r16 as i8
    }
}
// </vc-code>


}

fn main() {}