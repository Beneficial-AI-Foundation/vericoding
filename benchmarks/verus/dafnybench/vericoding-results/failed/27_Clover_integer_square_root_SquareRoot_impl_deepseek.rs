use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_mul_mono(a: int, b: int, c: int, d: int)
    requires
        a <= b,
        c <= d,
        0 <= a,
        0 <= c,
    ensures
        a * c <= b * d,
{
}

proof fn lemma_add_mono(a: int, b: int, c: int, d: int)
    requires
        a <= b,
        c <= d,
    ensures
        a + c <= b + d,
{
}

proof fn lemma_square_mono(a: int, b: int)
    requires
        0 <= a <= b,
    ensures
        a * a <= b * b,
{
    lemma_mul_mono(a, b, a, b);
}

proof fn lemma_add_one_mono(a: int, b: int)
    requires
        a <= b,
    ensures
        a + 1 <= b + 1,
{
}

proof fn lemma_square_add_one_mono(a: int, b: int)
    requires
        0 <= a <= b,
    ensures
        (a + 1) * (a + 1) <= (b + 1) * (b + 1),
{
    lemma_add_one_mono(a, b);
    lemma_mul_mono(a + 1, b + 1, a + 1, b + 1);
}

spec fn sqrt_spec(n: int) -> int
    recommends n >= 0
    ensures
        result >= 0,
        result * result <= n < (result + 1) * (result + 1),
{
    if n == 0 {
        0
    } else {
        let mut r = 0;
        while r * r <= n
            invariant
                0 <= r,
                r * r <= n,
        {
            r = r + 1;
        }
        r - 1
    }
}

proof fn sqrt_spec_correct(n: int)
    requires
        n >= 0,
    ensures
        sqrt_spec(n) * sqrt_spec(n) <= n < (sqrt_spec(n) + 1) * (sqrt_spec(n) + 1),
{
    if n == 0 {
        assert((0 + 1) * (0 + 1) > 0);
    } else {
        let mut r: int = 0;
        assert(r * r <= n);
        while r * r <= n
            invariant
                0 <= r,
                r * r <= n,
        {
            lemma_square_mono(r, r + 1);
            lemma_square_add_one_mono(r, r + 1);
            r = r + 1;
        }
        assert((r - 1) * (r - 1) <= n);
        assert(r * r > n);
    }
}
// </vc-helpers>

// <vc-spec>
fn square_root(n: u32) -> (r: u32)
  ensures r * r <= n < (r + 1) * (r + 1)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        proof {
            assert(0 * 0 <= 0 < (0 + 1) * (0 + 1));
        }
        0
    } else {
        let mut r: u32 = 0;
        while r * r <= n
            invariant
                0 <= r,
                r * r <= n,
        {
            r = r + 1;
        }
        let result = r - 1;
        proof {
            sqrt_spec_correct(n as int);
            assert(result as int * result as int <= n as int);
            assert((result as int + 1) * (result as int + 1) > n as int);
        }
        result
    }
}
// </vc-code>

fn main() {}

}