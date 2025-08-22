use vstd::prelude::*;

verus! {

#[verifier::memoize]
spec fn spec_fib(n: nat) -> (ret:nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        1
    } else {
        spec_fib((n - 1) as nat) + spec_fib((n - 2) as nat)
    }
}
// pure-end

proof fn lemma_fib_monotonic(i: nat, j: nat)
    // pre-conditions-start
    requires
        i <= j,
    // pre-conditions-end
    // post-conditions-start
    ensures
        spec_fib(i) <= spec_fib(j),
    decreases j - i,
    // post-conditions-end
{
    // impl-start
    if (i < 2 && j < 2) || i == j {
    } else if i == j - 1 {
        reveal_with_fuel(spec_fib, 2);
        lemma_fib_monotonic(i, (j - 1) as nat);
    } else {
        lemma_fib_monotonic(i, (j - 1) as nat);
        lemma_fib_monotonic(i, (j - 2) as nat);
    }
    // impl-end
}
// pure-end

spec fn inner_expr_fib(n: u32, ret: Option<u32>) -> (result:bool) {
    match ret {
        None => spec_fib(n as nat) > u32::MAX,
        Some(f) => f == spec_fib(n as nat),
    }
}
// pure-end

fn fib(n: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        inner_expr_fib(n, ret),
    // post-conditions-end
{
    // impl-start
    if n > 47 {
        // assert-start
        proof {
            assert(spec_fib(48) > u32::MAX) by (compute_only);
            lemma_fib_monotonic(48, n as nat);
        }
        // assert-end
        return None;
    }
    match n {
        0 => Some(0),
        1 => Some(1),
        _ => {
            // assert-start
            proof {
                assert(spec_fib(47) < u32::MAX) by (compute_only);
                lemma_fib_monotonic(n as nat, 47);
                lemma_fib_monotonic((n - 1) as nat, 47);
                lemma_fib_monotonic((n - 2) as nat, 47);
            }
            // assert-end
            let n1 = fib(n - 1)?;
            let n2 = fib(n - 2)?;
            Some(n1 + n2)
        },
    }
    // impl-end
}

} // verus!
fn main() {}
