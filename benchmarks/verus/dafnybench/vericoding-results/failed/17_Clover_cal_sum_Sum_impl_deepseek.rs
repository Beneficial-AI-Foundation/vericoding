use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_triangle_number(n: nat)
    ensures
        (n * (n + 1)) / 2 == (n as int) * ((n + 1) as int) / 2,
    decreases n,
{
    if n > 0 {
        lemma_triangle_number((n - 1) as nat);
    }
}

proof fn lemma_sum_formula(n: nat)
    ensures
        n * (n + 1) % 2 == 0,
    decreases n,
{
    if n > 0 {
        lemma_sum_formula((n - 1) as nat);
    }
}

proof fn lemma_div_by_2(n: nat)
    ensures
        (n * (n + 1)) % 2 == 0,
    decreases n,
{
    if n > 0 {
        lemma_div_by_2((n - 1) as nat);
    }
}

proof fn lemma_sum_identity(n: nat)
    ensures
        (n * (n + 1)) / 2 == ((n as int) * ((n + 1) as int)) / 2,
    decreases n,
{
    if n > 0 {
        lemma_sum_identity((n - 1) as nat);
    }
}

proof fn lemma_arithmetic_progression(i: nat)
    ensures
        (i as int) * ((i + 1) as int) / 2 == ((i as int) - 1) * (i as int) / 2 + (i as int),
{
    if i > 0 {
        lemma_div_by_2(i);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum(n: u32) -> (s: u32)
    requires n >= 0
    ensures s == n * (n + 1) / 2
// </vc-spec>
// <vc-code>
{
    let mut s: u32 = 0;
    let mut i: u32 = 0;
    while i <= n
        invariant
            i <= n + 1,
            s as int == (i as int) * ((i as int) - 1) / 2,
        decreases (n as int) - (i as int)
    {
        s = s + i;
        proof {
            lemma_arithmetic_progression(i as nat);
        }
        i = i + 1;
    }
    proof {
        lemma_sum_identity(n as nat);
    }
    s
}
// </vc-code>

fn main() {}

}