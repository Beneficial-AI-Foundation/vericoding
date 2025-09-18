// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): zero complex constructor retained for convenience */
pub open spec fn czero() -> Complex { Complex { re: 0, im: 0 } }

/* helper modified by LLM (iteration 5): lemma showing c * cexp(t) = c given cexp(t) = 1 */
proof fn lemma_mul_cexp_identity(c: Complex, t: int)
    ensures c.mul(cexp(t)) == c
{
    assert(c.mul(cexp(t)) == Complex { re: c.re * 1 - c.im * 0, im: c.re * 0 + c.im * 1 });
    assert(Complex { re: 1 * c.re - 0 * c.im, im: 0 * c.re + 1 * c.im } == c);
}

/* helper modified by LLM (iteration 5): lemma showing scalar multiplication by 1 preserves the value */
proof fn lemma_scalar_mul_one(c: Complex)
    ensures c.scalar_mul(1) == c
{
    assert(c.scalar_mul(1) == Complex { re: 1 * c.re, im: 1 * c.im });
    assert(Complex { re: 1 * c.re, im: 1 * c.im } == c);
}

/* helper modified by LLM (iteration 5): strengthened inductive lemma with proper case split on index relative to n_total */
proof fn lemma_sum_mul_cexp_is_sum(n: nat, n_total: nat, a: spec_fn(nat) -> Complex, k: int)
    ensures
        complex_sum(n, |j: nat| {
            if j < n_total { a(j).mul(cexp(2 * k * (j as int))) } else { Complex { re: 0, im: 0 } }
        }) ==
        complex_sum(n, |j: nat| {
            if j < n_total { a(j) } else { Complex { re: 0, im: 0 } }
        })
    decreases n
{
    if n == 0 {
    } else {
        let m = (n - 1) as nat;
        lemma_sum_mul_cexp_is_sum(m, n_total, a, k);
        let f1 = |j: nat| { if j < n_total { a(j).mul(cexp(2 * k * (j as int))) } else { Complex { re: 0, im: 0 } } };
        let f2 = |j: nat| { if j < n_total { a(j) } else { Complex { re: 0, im: 0 } } };
        if m < n_total {
            proof { lemma_mul_cexp_identity(a(m), 2 * k * (m as int)); }
            assert(f1(m) == a(m).mul(cexp(2 * k * (m as int))));
            assert(f2(m) == a(m));
            assert(f1(m) == f2(m));
        } else {
            assert(f1(m) == Complex { re: 0, im: 0 });
            assert(f2(m) == Complex { re: 0, im: 0 });
            assert(f1(m) == f2(m));
        }
        assert(complex_sum(n, f1) == f1(m).add(complex_sum(m, f1)));
        assert(complex_sum(n, f2) == f2(m).add(complex_sum(m, f2)));
        assert(complex_sum(m, f1) == complex_sum(m, f2));
        assert(f1(m).add(complex_sum(m, f1)) == f2(m).add(complex_sum(m, f2)));
        assert(complex_sum(n, f1) == complex_sum(n, f2));
    }
}

/* helper modified by LLM (iteration 5): lemma relating truncated sum to plain sum when n <= n_total */
proof fn lemma_sum_truncate_matches_plain(n: nat, n_total: nat, a: spec_fn(nat) -> Complex)
    requires n <= n_total
    ensures complex_sum(n, |j: nat| { if j < n_total { a(j) } else { Complex { re: 0, im: 0 } } }) == complex_sum(n, a)
    decreases n
{
    if n == 0 {
    } else {
        let m = (n - 1) as nat;
        lemma_sum_truncate_matches_plain(m, n_total, a);
        let f_tr = |j: nat| { if j < n_total { a(j) } else { Complex { re: 0, im: 0 } } };
        assert(complex_sum(n, f_tr) == f_tr(m).add(complex_sum(m, f_tr)));
        assert(complex_sum(n, a) == a(m).add(complex_sum(m, a)));
        assert(m < n_total) by {
            assert(m < n);
            assert(n <= n_total);
        };
        assert(f_tr(m) == a(m));
        assert(complex_sum(m, f_tr) == complex_sum(m, a));
        assert(f_tr(m).add(complex_sum(m, f_tr)) == a(m).add(complex_sum(m, a)));
        assert(complex_sum(n, f_tr) == complex_sum(n, a));
    }
}
// </vc-helpers>

// <vc-spec>
#[derive(PartialEq, Eq, Structural)]
pub struct Complex {
    pub re: int,
    pub im: int,
}

impl Complex {
    pub open spec fn add(self, other: Complex) -> Complex {
        Complex { re: self.re + other.re, im: self.im + other.im }
    }

    pub open spec fn mul(self, other: Complex) -> Complex {
        Complex { 
            re: self.re * other.re - self.im * other.im, 
            im: self.re * other.im + self.im * other.re 
        }
    }

    pub open spec fn scalar_mul(self, s: int) -> Complex {
        Complex { re: s * self.re, im: s * self.im }
    }
}

pub open spec fn cexp(theta: int) -> Complex {
    Complex { re: 1, im: 0 }
}

pub open spec fn complex_sum(n: nat, f: spec_fn(nat) -> Complex) -> Complex
    decreases n
{
    if n == 0 {
        Complex { re: 0, im: 0 }
    } else {
        f((n - 1) as nat).add(complex_sum((n - 1) as nat, f))
    }
}

fn ifft(a: Vec<Complex>) -> (result: Vec<Complex>)
    requires a.len() > 0,
    ensures
        result.len() == a.len(),
        forall|k: int| #[trigger] result[k] == result[k] && 0 <= k < result.len() ==> {
            let n = a.len() as nat;
            let expected = complex_sum(n, |j: nat| {
                if j < n {
                    a[j as int].mul(cexp(2 * k * (j as int)))
                } else {
                    Complex { re: 0, im: 0 }
                }
            }).scalar_mul(1);
            result[k] == expected
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed closure braces in invariants and replaced a@ with spec indexing using a[...] */
    let n_usize = a.len();
    let n_int: int = n_usize as int;
    let n_nat: nat = n_usize as nat;

    let mut i: int = 0;
    let mut sum = Complex { re: 0, im: 0 };
    while i < n_int
        invariant 0 <= i <= n_int
        invariant sum == complex_sum(i as nat, |j: nat| { a[j as int] })
        decreases n_int - i
    {
        let ai = a[i as usize];
        sum = Complex { re: sum.re + ai.re, im: sum.im + ai.im };
        i = i + 1;
    }

    let mut out: Vec<Complex> = Vec::new();
    let mut j: int = 0;
    while j < n_int
        invariant 0 <= j <= n_int
        invariant out.len() as int == j
        invariant forall|t: int| 0 <= t < out.len() as int ==> out[t] == sum
        decreases n_int - j
    {
        out.push(sum);
        j = j + 1;
    }

    proof {
        assert(sum == complex_sum(n_nat, |j: nat| { a[j as int] }));

        assert_forall_by(|k: int| {
            requires 0 <= k < out.len() as int;
            ensures {
                let n = a.len() as nat;
                let expected = complex_sum(n, |j: nat| {
                    if j < n {
                        a[j as int].mul(cexp(2 * k * (j as int)))
                    } else {
                        Complex { re: 0, im: 0 }
                    }
                }).scalar_mul(1);
                out[k] == expected
            };

            assert(out[k] == sum);

            let csum_plain_noif = complex_sum(n_nat, |j: nat| { a[j as int] });
            assert(sum == csum_plain_noif);

            let csum_plain_trunc = complex_sum(n_nat, |j: nat| {
                if j < n_nat { a[j as int] } else { Complex { re: 0, im: 0 } }
            });
            let csum_mul = complex_sum(n_nat, |j: nat| {
                if j < n_nat { a[j as int].mul(cexp(2 * k * (j as int))) } else { Complex { re: 0, im: 0 } }
            });

            proof { lemma_sum_mul_cexp_is_sum(n_nat, n_nat, |j: nat| { a[j as int] }, k); }
            assert(csum_mul == csum_plain_trunc);

            proof { lemma_sum_truncate_matches_plain(n_nat, n_nat, |j: nat| { a[j as int] }); }
            assert(csum_plain_trunc == csum_plain_noif);

            assert(csum_mul.scalar_mul(1) == csum_plain_noif.scalar_mul(1));
            proof { lemma_scalar_mul_one(csum_plain_noif); }
            assert(csum_plain_noif.scalar_mul(1) == csum_plain_noif);

            assert(out[k] == csum_mul.scalar_mul(1));
        });
    }

    out
}
// </vc-code>

}
fn main() {}