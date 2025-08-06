
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {


spec fn factorial(n: nat) -> (ret:nat)
    decreases n,
{
    if n <= 1 {
        1
    } else {
        n * factorial((n - 1) as nat)
    }
}
// pure-end

spec fn brazilian_factorial(n: nat) -> (ret:nat)
    decreases n,
{
    if n <= 1 {
        factorial(1)
    } else {
        factorial(n) * brazilian_factorial((n - 1) as nat)
    }
}
// pure-end

proof fn lemma_factorial_positive(n: nat)
    // post-conditions-start
    ensures
        factorial(n) >= 1,
    decreases n,
    // post-conditions-end
{
    // impl-start
    if (n == 0) {
    } else {
        lemma_factorial_positive((n - 1) as nat);
        assert(factorial(n) >= 1) by {
            broadcast use lemma_mul_strictly_positive;

        };
    }
    // impl-end
}
// pure-end

proof fn lemma_brazilian_factorial_positive(n: nat)
    // post-conditions-start
    ensures
        brazilian_factorial(n) >= 1,
    decreases n,
    // post-conditions-end
{
    // impl-start
    if (n == 0) {
    } else {
        lemma_factorial_positive((n) as nat);
        lemma_brazilian_factorial_positive((n - 1) as nat);
        assert(brazilian_factorial(n) >= 1) by {
            lemma_mul_strictly_positive(
                factorial(n) as int,
                brazilian_factorial((n - 1) as nat) as int,
            )
        };
    }
    // impl-end
}
// pure-end

proof fn lemma_brazilian_fib_monotonic(i: nat, j: nat)
    // pre-conditions-start
    requires
        0 <= i <= j,
    // pre-conditions-end
    // post-conditions-start
    ensures
        brazilian_factorial(i) <= brazilian_factorial(j),
    decreases j - i,
    // post-conditions-end
{
    // impl-start
    if (i == j) {
    } else if (j == i + 1) {
        assert(factorial(j) >= 1) by { lemma_factorial_positive(j) };
        assert(brazilian_factorial(j) >= brazilian_factorial(i)) by {
            broadcast use lemma_mul_increases;

        };
    } else {
        lemma_brazilian_fib_monotonic(i, (j - 1) as nat);
        lemma_brazilian_fib_monotonic((j - 1) as nat, j);
    }
    // impl-end
}
// pure-end

fn brazilian_factorial_impl(n: u64) -> (ret: Option<u64>)
    // post-conditions-start
    ensures
        match ret {
    return None;  // TODO: Remove this line and implement the function body
        },
    // post-conditions-end
{
    // impl-start
    if n >= 9 {
        // assert-start
        assert(brazilian_factorial(9nat) > u64::MAX) by (compute_only);
        assert(brazilian_factorial(n as nat) >= brazilian_factorial(9nat)) by {
            lemma_brazilian_fib_monotonic(9nat, n as nat)
        };
        // assert-end
        return None;
    }
    let mut start = 1u64;
    let mut end = n + 1u64;
    let mut fact_i = 1u64;
    let mut special_fact = 1u64;

    while start < end
        // invariants-start
        invariant
            brazilian_factorial((start - 1) as nat) == special_fact,
            factorial((start - 1) as nat) == fact_i,
            1 <= start <= end < 10,
        decreases (end - start),
        // invariants-end
    {
        // assert-start
        assert(brazilian_factorial(start as nat) <= brazilian_factorial(8nat)) by {
            lemma_brazilian_fib_monotonic(start as nat, 8nat)
        };
        assert(brazilian_factorial(8nat) < u64::MAX) by (compute_only);

        assert(brazilian_factorial((start - 1) as nat) >= 1) by {
            lemma_brazilian_factorial_positive((start - 1) as nat)
        };
        assert(factorial(start as nat) <= brazilian_factorial(start as nat)) by {
            broadcast use lemma_mul_ordering;

        };
        // assert-end

        fact_i = start * fact_i;

        special_fact = fact_i * special_fact;

        start = start + 1;
    }
    return Some(special_fact);
    // impl-end

}

} // verus!
fn main() {}
