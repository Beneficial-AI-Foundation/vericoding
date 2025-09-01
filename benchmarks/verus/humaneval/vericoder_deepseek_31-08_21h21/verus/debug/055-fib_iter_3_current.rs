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
// pure-end

spec fn inner_expr_fib(n: u32, ret: Option<u32>) -> (result:bool) {
    match ret {
        None => spec_fib(n as nat) > u32::MAX,
        Some(f) => f == spec_fib(n as nat),
    }
}
// pure-end

// <vc-helpers>
proof fn lemma_fib_mono(x: nat, y: nat)
    requires
        x <= y,
    ensures
        spec_fib(x) <= spec_fib(y),
    decreases y,
{
    if x < y {
        lemma_fib_mono(x, (y - 1) as nat);
    }
}

proof fn lemma_fib_bounds(n: nat)
    ensures
        spec_fib(n) <= spec_fib((n + 1) as nat),
    decreases n,
{
    if n > 0 {
        lemma_fib_bounds((n - 1) as nat);
    }
}

proof fn lemma_fib_overflow_bound(n: nat)
    requires
        n >= 48,
    ensures
        spec_fib(n) > u32::MAX,
{
    if n == 48 {
    } else {
        lemma_fib_overflow_bound((n - 1) as nat);
        lemma_fib_mono(48, n);
    }
}

proof fn lemma_fib_specific_values()
    ensures
        spec_fib(0 as nat) == 0,
        spec_fib(1 as nat) == 1,
        spec_fib(2 as nat) == 1,
        spec_fib(3 as nat) == 2,
        spec_fib(4 as nat) == 3,
        spec_fib(5 as nat) == 5,
        spec_fib(6 as nat) == 8,
        spec_fib(7 as nat) == 13,
        spec_fib(8 as nat) == 21,
        spec_fib(9 as nat) == 34,
        spec_fib(10 as nat) == 55,
        spec_fib(11 as nat) == 89,
        spec_fib(12 as nat) == 144,
        spec_fib(13 as nat) == 233,
        spec_fib(14 as nat) == 377,
        spec_fib(15 as nat) == 610,
        spec_fib(16 as nat) == 987,
        spec_fib(17 as nat) == 1597,
        spec_fib(18 as nat) == 2584,
        spec_fib(19 as nat) == 4181,
        spec_fib(20 as nat) == 6765,
        spec_fib(21 as nat) == 10946,
        spec_fib(22 as nat) == 17711,
        spec_fib(23 as nat) == 28657,
        spec_fib(24 as nat) == 46368,
        spec_fib(25 as nat) == 75025,
        spec_fib(26 as nat) == 121393,
        spec_fib(27 as nat) == 196418,
        spec_fib(28 as nat) == 317811,
        spec_fib(29 as nat) == 514229,
        spec_fib(30 as nat) == 832040,
        spec_fib(31 as nat) == 1346269,
        spec_fib(32 as nat) == 2178309,
        spec_fib(33 as nat) == 3524578,
        spec_fib(34 as nat) == 5702887,
        spec_fib(35 as nat) == 9227465,
        spec_fib(36 as nat) == 14930352,
        spec_fib(37 as nat) == 24157817,
        spec_fib(38 as nat) == 39088169,
        spec_fib(39 as nat) == 63245986,
        spec_fib(40 as nat) == 102334155,
        spec_fib(41 as nat) == 165580141,
        spec_fib(42 as nat) == 267914296,
        spec_fib(43 as nat) == 433494437,
        spec_fib(44 as nat) == 701408733,
        spec_fib(45 as nat) == 1134903170,
        spec_fib(46 as nat) == 1836311903,
        spec_fib(47 as nat) == 2971215073,
        spec_fib(48 as nat) == 4807526976,
{
    reveal(spec_fib);
}
// </vc-helpers>

// <vc-spec>
fn fib(n: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        inner_expr_fib(n, ret),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if n >= 48 {
        proof {
            lemma_fib_overflow_bound(n as nat);
        }
        None
    } else {
        let mut a: u32 = 0;
        let mut b: u32 = 1;
        let mut i: u32 = 0;
        
        while i < n
            invariant
                i <= n,
                a == spec_fib(i as nat),
                b == spec_fib((i + 1) as nat),
        {
            proof {
                lemma_fib_specific_values();
            }
            let next = a.checked_add(b);
            match next {
                Some(sum) => {
                    a = b;
                    b = sum;
                }
                None => {
                    return None;
                }
            }
            i += 1;
        }
        
        Some(a)
    }
}
// </vc-code>

} // verus!
fn main() {}