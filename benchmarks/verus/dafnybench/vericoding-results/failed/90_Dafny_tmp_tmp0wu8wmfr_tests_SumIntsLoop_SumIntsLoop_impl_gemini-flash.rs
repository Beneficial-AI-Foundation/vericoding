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
fn sum_ints_formula(n: int) -> int {
    n * (n + 1) / 2
}

proof fn lemma_sum_ints_formula_correct(n: nat)
    ensures sum_ints(n as int) == sum_ints_formula(n as int)
    decreases n
{
    if n == 0 {
        assert(sum_ints(0) == 0);
        assert(sum_ints_formula(0) == 0);
    } else {
        lemma_sum_ints_formula_correct((n - 1) as nat);
        assert(sum_ints(n as int) == sum_ints((n - 1) as int) + n as int);
        assert(sum_ints((n - 1) as int) == sum_ints_formula((n - 1) as int));
        assert(sum_ints_formula((n - 1) as int) + n as int == (n - 1) * n / 2 + n as int);
        // Additional assertions to prove algebraic equivalence
        assert((n - 1) * n / 2 + n as int == (n * n - n + 2 * n) / 2);
        assert((n * n - n + 2 * n) / 2 == (n * n + n) / 2);
        assert((n * n + n) / 2 == n * (n + 1) / 2);
    }
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
    let mut i: u32 = 0;
    let mut s: u32 = 0;

    reveal(sum_ints_formula); 

    proof {
        lemma_sum_ints_formula_correct(n as nat);
    }

    while i < n
        invariant
            0 <= i as int,
            i <= n,
            s as int == sum_ints(i as int),
            s as int == sum_ints_formula(i as int),
            s as int == i as int * (i as int + 1) / 2,
    {
        s = s + (i + 1);
        i = i + 1;
    }
    assert(s as int == sum_ints(n as int));
    assert(s as int == n as int * (n as int + 1) / 2);
    s
}
// </vc-code>

fn main() {
}

}