// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn complex_sum_zero(n: nat)
    ensures
        complex_sum(n, |_j| Complex { re: 0, im: 0 }) == (Complex { re: 0, im: 0 }),
{
    if n > 0 {
        complex_sum_zero((n - 1) as nat);
    }
}

proof fn complex_sum_additive(n: nat, f: spec_fn(nat) -> Complex, g: spec_fn(nat) -> Complex)
    ensures
        complex_sum(n, |j| f(j).add(g(j))) == complex_sum(n, f).add(complex_sum(n, g)),
{
    if n > 0 {
        complex_sum_additive((n - 1) as nat, f, g);
    }
}

proof fn complex_sum_scalar(n: nat, f: spec_fn(nat) -> Complex, s: int)
    ensures
        complex_sum(n, |j| f(j).scalar_mul(s)) == complex_sum(n, f).scalar_mul(s),
{
    if n > 0 {
        complex_sum_scalar((n - 1) as nat, f, s);
    }
}

proof fn complex_sum_constant(n: nat, c: Complex)
    ensures
        complex_sum(n, |_j| c) == c.scalar_mul(n as int),
{
    if n > 0 {
        complex_sum_constant((n - 1) as nat, c);
    }
}

/* helper modified by LLM (iteration 5): fix int conversion in loop invariants */
proof fn complex_sum_index_helper(n: nat, a: Seq<Complex>, k: int)
    requires
        n > 0,
        k >= 0,
    ensures
        complex_sum(n, |j: nat| {
            if j < n {
                a[j as int].mul(cexp(2 * k * (j as int)))
            } else {
                Complex { re: 0, im: 0 }
            }
        }) == complex_sum(n, |j: nat| {
            if j < n {
                a[j as int].mul(cexp(2 * (k as int) * (j as int)))
            } else {
                Complex { re: 0, im: 0 }
            }
        }),
{
    if n > 1 {
        complex_sum_index_helper((n - 1) as nat, a, k);
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
    /* code modified by LLM (iteration 5): fix int cast errors by using proof blocks for ghost code */
    let n = a.len();
    let mut result = Vec::new();
    let mut k: usize = 0;
    
    while k < n
        invariant
            k <= n,
            result.len() == k,
            forall|i: int| 0 <= i < k ==> {
                let n_nat = n as nat;
                let expected = complex_sum(n_nat, |j: nat| {
                    if j < n_nat {
                        let ji = j as int;
                        let ii = i;
                        proof {
                            complex_sum_index_helper(n_nat, a@, ii);
                        }
                        a[j as int].mul(cexp(2 * ii * ji))
                    } else {
                        (Complex { re: 0, im: 0 })
                    }
                }).scalar_mul(1);
                result[i] == expected
            }
    {
        let mut sum = (Complex { re: 0, im: 0 });
        let mut j: usize = 0;
        
        while j < n
            invariant
                j <= n,
                sum == complex_sum(j as nat, |jj: nat| {
                    if jj < n as nat {
                        let jj_i = jj as int;
                        let k_i = k as int;
                        proof {
                            complex_sum_index_helper(j as nat, a@, k_i);
                        }
                        a[jj as int].mul(cexp(2 * k_i * jj_i))
                    } else {
                        (Complex { re: 0, im: 0 })
                    }
                })
        {
            let term = proof {
                let j_i = j as int;
                let k_i = k as int;
                a[j].mul(cexp(2 * k_i * j_i))
            };
            sum = sum.add(term);
            j += 1;
        }
        
        result.push(sum.scalar_mul(1));
        k += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}