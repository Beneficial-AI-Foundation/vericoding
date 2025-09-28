use vstd::prelude::*;

verus! {

spec fn sum_ints(n: int) -> int
    decreases n when n >= 0
{
    if n <= 0 {
        0
    } else {
        sum_ints(n - 1) + n
    }
}

// <vc-helpers>
proof fn lemma_sum_ints_formula(n: nat)
    ensures
        sum_ints(n as int) == n * (n + 1) / 2,
    decreases n
{
    if n > 0 {
        lemma_sum_ints_formula((n - 1) as nat);
    }
}

proof fn lemma_mult_div_commutative(m: nat, n: nat)
    requires
        n > 0,
    ensures
        m * n / n == m,
{
}

proof fn lemma_sum_ints_positive(n: nat)
    ensures
        sum_ints(n as int) >= 0,
    decreases n
{
    if n > 0 {
        lemma_sum_ints_positive((n - 1) as nat);
    }
}

proof fn lemma_div_by_2_commutative(n: nat)
    requires
        n >= 0,
    ensures
        n * (n + 1) / 2 == (n * (n + 1)) / 2,
{
}

proof fn lemma_sum_ints_step(i: nat)
    ensures
        sum_ints(i as int) + (i + 1) == sum_ints((i + 1) as int),
    decreases i
{
    reveal(sum_ints);
}

proof fn lemma_arithmetic_formula(i: nat)
    ensures
        i * (i + 1) / 2 + (i + 1) == (i + 1) * (i + 2) / 2,
{
    assert((i * (i + 1) + 2 * (i + 1)) == (i + 1) * (i + 2));
}
// </vc-helpers>

// <vc-spec>
fn sum_ints_loop(n: u32) -> (s: u32)
    ensures 
        s == sum_ints(n as int),
        s == n * (n + 1) / 2;
// </vc-spec>
// <vc-code>
{
    let mut s: u32 = 0;
    let mut i: u32 = 0;
    
    while i < n
        invariant
            i <= n,
            s == sum_ints(i as int),
            s == i * (i + 1) / 2,
    {
        s = s + (i + 1);
        i = i + 1;
        
        proof {
            lemma_sum_ints_step((i - 1) as nat);
            lemma_arithmetic_formula((i - 1) as nat);
        }
    }
    
    proof {
        lemma_sum_ints_formula(n as nat);
    }
    
    s
}
// </vc-code>

fn main() {
}

}