use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_div_mul_identity(x: int, d: int)
    requires
        d > 0,
        x % d == 0,
    ensures
        x / d * d == x
{
}

proof fn lemma_mul_div_identity(x: int, d: int)
    requires
        d > 0,
    ensures
        x * d / d == x
{
}

proof fn lemma_div2_multiplication(x: int)
    requires
        x >= 0,
    ensures
        x * 2 / 2 == x
{
    lemma_mul_div_identity(x, 2);
}

proof fn lemma_7n_minus_5_nonnegative(n: int)
    requires
        n >= 0,
    ensures
        7 * n - 5 >= -5,
    decreases {
}

proof fn lemma_nth_nonagonal_step(i: int)
    requires
        i >= 0,
    ensures
        (i * (7 * i - 5) + 2 * (7 * i - 5)) / 2 == (i + 1) * (7 * (i + 1) - 5) / 2 - 3,
{
    assert((i * (7 * i - 5) + 2 * (7 * i - 5)) / 2 == (7*i*i -5*i + 14*i -10) / 2);
    assert((7*i*i -5*i + 14*i -10) / 2 == (7*i*i + 9*i -10) / 2);
    assert((7*i*i + 9*i -10) / 2 == (7*(i+1)*(i+1) - 5*(i+1) - 6) / 2);
    assert((7*(i+1)*(i+1) - 5*(i+1) - 6) / 2 == ((i+1) * (7*(i+1) - 5) - 6) / 2);
    assert(((i+1) * (7*(i+1) - 5) - 6) / 2 == (i+1) * (7*(i+1) - 5) / 2 - 3);
}
// </vc-helpers>

// <vc-spec>
fn nth_nonagonal_number(n: int) -> (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    }

    let mut i = 0;
    let mut sum = 0;
    
    while i < n 
        invariant 
            0 <= i <= n,
            sum == i * (7 * i - 5) / 2,
        decreases n - i
    {
        lemma_7n_minus_5_nonnegative(i);
        
        let next_i = i + 1;
        let term = 7 * i - 5;
        sum = sum + term;
        
        proof {
            lemma_nth_nonagonal_step(i);
        }
        
        sum = sum + 3;
        i = next_i;
    }
    
    sum
}
// </vc-code>

fn main() {}

}