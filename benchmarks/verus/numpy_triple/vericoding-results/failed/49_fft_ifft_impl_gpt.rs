// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemmas to reason about Complex operations and complex_sum, with explicit int/nat literals */
proof fn lemma_mul_one(c: Complex)
    ensures
        c.mul(Complex { re: 1int, im: 0int }) == c,
{
    assert(c.mul(Complex { re: 1int, im: 0int }).re == c.re * 1int - c.im * 0int);
    assert(c.mul(Complex { re: 1int, im: 0int }).im == c.re * 0int + c.im * 1int);
    assert(c.re * 1int - c.im * 0int == c.re);
    assert(c.re * 0int + c.im * 1int == c.im);
}

/* helper modified by LLM (iteration 5): relate field-wise addition to spec add */
proof fn lemma_add_def(x: Complex, y: Complex)
    ensures
        x.add(y) == Complex { re: x.re + y.re, im: x.im + y.im },
{
}

/* helper modified by LLM (iteration 5): scalar multiplication by 1 leaves Complex unchanged */
proof fn lemma_scalar_mul_one(c: Complex)
    ensures
        c.scalar_mul(1int) == c,
{
    assert(c.scalar_mul(1int).re == 1int * c.re);
    assert(c.scalar_mul(1int).im == 1int * c.im);
    assert(1int * c.re == c.re);
    assert(1int * c.im == c.im);
}

/* helper modified by LLM (iteration 5): adding zero on the right leaves Complex unchanged */
proof fn lemma_add_zero_right(c: Complex)
    ensures
        c.add(Complex { re: 0int, im: 0int }) == c,
{
    assert(c.add(Complex { re: 0int, im: 0int }).re == c.re + 0int);
    assert(c.add(Complex { re: 0int, im: 0int }).im == c.im + 0int);
}

/* helper modified by LLM (iteration 5): extensionality of complex_sum under pointwise equality */
proof fn lemma_complex_sum_extensional(n: nat, f: spec_fn(nat) -> Complex, g: spec_fn(nat) -> Complex)
    requires
        forall|j: nat| j < n ==> f(j) == g(j),
    ensures
        complex_sum(n, f) == complex_sum(n, g),
    decreases n
{
    if n == 0nat {
        // complex_sum(0, _) is zero for both f and g
    } else {
        let m: nat = (n - 1) as nat;
        assert(f(m) == g(m));
        lemma_complex_sum_extensional(m, f, g);
        assert(complex_sum(n, f) == f(m).add(complex_sum(m, f)));
        assert(complex_sum(n, g) == g(m).add(complex_sum(m, g)));
        assert(complex_sum(m, f) == complex_sum(m, g));
        assert(f(m).add(complex_sum(m, f)) == g(m).add(complex_sum(m, g)));
    }
}

/* helper modified by LLM (iteration 5): cexp is 1, so terms simplify inside complex_sum */
proof fn lemma_complex_sum_cexp_one(n: nat, a: Vec<Complex>, k: int)
    requires
        n == a.len() as nat,
    ensures
        complex_sum(n, |j: nat| {
            if j < n {
                a[j as int].mul(cexp(2 * k * (j as int)))
            } else {
                Complex { re: 0int, im: 0int }
            }
        }) ==
        complex_sum(n, |j: nat| {
            if j < n {
                a[j as int]
            } else {
                Complex { re: 0int, im: 0int }
            }
        }),
    decreases n
{
    let f = |j: nat| {
        if j < n {
            a[j as int].mul(cexp(2 * k * (j as int)))
        } else {
            Complex { re: 0int, im: 0int }
        }
    };
    let g = |j: nat| {
        if j < n {
            a[j as int]
        } else {
            Complex { re: 0int, im: 0int }
        }
    };
    assert forall|j: nat| j < n implies f(j) == g(j) by {
        assert(cexp(2 * k * (j as int)) == Complex { re: 1int, im: 0int });
        lemma_mul_one(a[j as int]);
        assert(f(j) == a[j as int].mul(Complex { re: 1int, im: 0int }));
        assert(a[j as int].mul(Complex { re: 1int, im: 0int }) == a[j as int]);
    };
    lemma_complex_sum_extensional(n, f, g);
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
/* code modified by LLM (iteration 5): avoid calling spec add in exec code; use field-wise addition and relate via lemma_add_def */
{
    // Initialize running sum from the first element to avoid constructing a zero Complex in exec code
    let mut i: usize = 1;
    let mut sum: Complex = a[0];

    // Establish loop invariant base: sum equals complex_sum over the first element
    proof {
        let f0 = |j: nat| if j < 1nat { a[j as int] } else { Complex { re: 0int, im: 0int } };
        assert(complex_sum(1nat, f0) == f0(0nat).add(complex_sum(0nat, f0)));
        assert(complex_sum(0nat, f0) == Complex { re: 0int, im: 0int });
        lemma_add_zero_right(f0(0nat));
        assert(f0(0nat).add(Complex { re: 0int, im: 0int }) == f0(0nat));
        assert(sum == complex_sum(1nat, f0));
    }

    while i < a.len()
        invariant
            1 <= i,
            i <= a.len(),
            sum == complex_sum(i as nat, |j: nat| {
                if j < i as nat {
                    a[j as int]
                } else {
                    Complex { re: 0int, im: 0int }
                }
            }),
        decreases a.len() - i
    {
        let old_sum = sum;
        let c = a[i];
        // Perform exec addition field-wise (cannot call spec add here)
        let new_sum = Complex { re: old_sum.re + c.re, im: old_sum.im + c.im };
        sum = new_sum;
        proof {
            // Connect field-wise addition with spec add for reasoning
            lemma_add_def(old_sum, c);
            assert(sum == old_sum.add(c));

            let prev_i: nat = i as nat;
            let next_i: nat = (i + 1) as nat;
            let f_prev = |j: nat| if j < prev_i { a[j as int] } else { Complex { re: 0int, im: 0int } };
            let f_next = |j: nat| if j < next_i { a[j as int] } else { Complex { re: 0int, im: 0int } };
            assert forall|j: nat| j < prev_i implies f_prev(j) == f_next(j) by { };
            lemma_complex_sum_extensional(prev_i, f_prev, f_next);
            assert(complex_sum(next_i, f_next) == f_next(prev_i).add(complex_sum(prev_i, f_next)));
            assert(f_next(prev_i) == a[prev_i as int]);
            assert(old_sum == complex_sum(prev_i, f_prev));
            assert(complex_sum(prev_i, f_prev) == complex_sum(prev_i, f_next));
            assert(sum == complex_sum(next_i, f_next));
        }
        i = i + 1;
    }

    proof {
        assert(i == a.len());
        let n: nat = a.len() as nat;
        let f_n = |j: nat| if j < n { a[j as int] } else { Complex { re: 0int, im: 0int } };
        assert(sum == complex_sum(n, f_n));
    }

    let total: Complex = sum;

    // Build the result vector by repeating `total` for each position
    let mut result: Vec<Complex> = Vec::new();
    let mut j: usize = 0;
    while j < a.len()
        invariant
            j <= a.len(),
            result.len() == j,
            forall|k: int| 0 <= k < result.len() ==> result[k] == total,
        decreases a.len() - j
    {
        result.push(total);
        j = j + 1;
    }

    proof {
        let n0: nat = a.len() as nat;
        assert(result.len() == a.len());
        assert forall|k: int| #[trigger] result[k] == result[k] && 0 <= k < result.len() implies {
            let expected_expr = complex_sum(n0, |jj: nat| {
                if jj < n0 {
                    a[jj as int].mul(cexp(2 * k * (jj as int)))
                } else {
                    Complex { re: 0int, im: 0int }
                }
            }).scalar_mul(1int);
            result[k] == expected_expr
        } by {
            assert(0 <= k < result.len() ==> result[k] == total);
            if 0 <= k < result.len() {
                assert(result[k] == total);
                let f_sum = complex_sum(n0, |jj: nat| {
                    if jj < n0 {
                        a[jj as int].mul(cexp(2 * k * (jj as int)))
                    } else {
                        Complex { re: 0int, im: 0int }
                    }
                });
                let simple_sum = complex_sum(n0, |jj: nat| {
                    if jj < n0 { a[jj as int] } else { Complex { re: 0int, im: 0int } }
                });
                lemma_complex_sum_cexp_one(n0, a, k);
                lemma_scalar_mul_one(f_sum);
                assert(f_sum.scalar_mul(1int) == f_sum);
                assert(f_sum == simple_sum);
                assert(f_sum.scalar_mul(1int) == simple_sum);
                assert(total == simple_sum);
            }
        }
    }

    result
}
// </vc-code>

}
fn main() {}