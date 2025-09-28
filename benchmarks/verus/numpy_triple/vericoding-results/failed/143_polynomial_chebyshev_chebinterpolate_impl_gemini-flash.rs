// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes, just preserving. */
proof fn lemma_constant_function_zero_deriv(func: spec_fn(f64) -> f64)
    requires
        is_constant_function(func),
    ensures
        forall|x: f64| func(x) == func(0.0),
{
    // Since func is constant, func(x) == func(y) for any x, y.
    // In particular, func(x) == func(0.0) for any x.
}
// </vc-helpers>

// <vc-spec>
spec fn is_constant_function(func: spec_fn(f64) -> f64) -> bool {
    forall|x: f64, y: f64| #[trigger] func(x) == #[trigger] func(y)
}

fn chebinterpolate(deg: usize, func: spec_fn(f64) -> f64) -> (coef: Vec<f64>)
    ensures 
        coef.len() == deg + 1,
        /* The coefficients satisfy the key properties of Chebyshev interpolation:
           1. The coefficient vector has the correct length (guaranteed by type)
           2. When the function is constant, all coefficients except the first are zero */
        is_constant_function(func) ==> (
            coef[0] == func(0.0) &&
            forall|i: int| 1 <= i < coef.len() ==> #[trigger] coef[i] == 0.0
        )
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatch in invariant (j: int to j: usize) */
{
    let N: usize = deg;
    let mut c: Vec<f64> = Vec::new();
    c.reserve(N + 1);
    proof {
        if (is_constant_function(func)) {
            lemma_constant_function_zero_deriv(func);
        }
    }

    let mut i: usize = 0; // Loop variable for coefficient index
    let mut alpha_i: f64;

    // Calculate the coefficients using the provided formula
    while i <= N
        invariant
            i <= N + 1,
            c.len() == i,
            c.capacity() >= N + 1,
            (is_constant_function(func) && i > 0) ==> (forall |j: usize| 0 <= j && j < i ==> c@[j] == if j == 0 {func(0.0)} else {0.0}),
            // For the first coefficient when function is constant
            (is_constant_function(func) && i == 1) ==> c@[0] == func(0.0)
        decreases (N as int) + 1 - (i as int)
    {
        alpha_i = 0.0;
        let mut j: usize = 0; // Loop variable for summation

        while j <= N
            invariant
                j <= N + 1,
                // For a constant function, T_i(x_j) will cancel out for i > 0 in the sum (because cos(i*theta) sums to 0)
                // The invariant for alpha_i's value is difficult to express precisely for a constant function within the loop
                // without knowing the cosine properties, so we maintain the general invariant without specific values.
            decreases (N as int) + 1 - (j as int)
        {
            let theta_j: f64 = (std::f64::consts::PI * (j as f64 + 0.5)) / (N as f64 + 1.0);
            let x_j: f64 = theta_j.cos();
            let T_i_x_j: f64 = (i as f64 * theta_j).cos(); // Chebyshev polynomial T_i(x_j)

            alpha_i = alpha_i + func(x_j) * T_i_x_j;

            j = j + 1;
        }

        alpha_i = alpha_i * (2.0 / (N as f64 + 1.0));

        if i == 0 {
            alpha_i = alpha_i / 2.0;
        }

        c.push(alpha_i);

        proof {
            if is_constant_function(func) {
                if i == 0 {
                    // When function is constant, func(x_j) = func(0.0)
                    // So alpha_0 = (1 / (N+1)) * sum(func(0.0)) = (1 / (N+1)) * (N+1) * func(0.0) = func(0.0)
                    assert(alpha_i == func(0.0));
                } else {
                    // For i > 0, sum_{j=0}^{N} cos(i * (pi * (j + 0.5) / (N+1))) == 0 (property of Chebyshev nodes)
                    // Thus alpha_i = 0 for i > 0 when the function is constant
                    assert(alpha_i == 0.0);
                }
            }
        }
        i = i + 1;
    }

    c
}
// </vc-code>


}
fn main() {}