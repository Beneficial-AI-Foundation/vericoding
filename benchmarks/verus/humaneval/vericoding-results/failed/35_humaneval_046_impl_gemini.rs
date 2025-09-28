// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn fib4_func(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n < 0 { 0 }
    else if n == 0 { 0 }
    else if n == 1 { 0 }
    else if n == 2 { 2 }
    else if n == 3 { 0 }
    else { fib4_func(n-1) + fib4_func(n-2) + fib4_func(n-3) + fib4_func(n-4) }
}
// </vc-preamble>

// <vc-helpers>
#[verifier::spinoff_prover]
proof fn lemma_fib4_nonnegative(n: int)
    requires n >= 0
    ensures fib4_func(n) >= 0
    decreases n
{
    if n >= 4 {
        lemma_fib4_nonnegative(n - 1);
        lemma_fib4_nonnegative(n - 2);
        lemma_fib4_nonnegative(n - 3);
        lemma_fib4_nonnegative(n - 4);
    }
}

proof fn lemma_fib4_nondecreasing_from_4(n: int)
    requires n >= 4
    ensures fib4_func(n) >= fib4_func(n - 1)
    decreases n
{
    lemma_fib4_nonnegative(n - 2);
    lemma_fib4_nonnegative(n - 3);
    lemma_fib4_nonnegative(n - 4);
}

proof fn lemma_fib4_monotonic_from_4(i: int, j: int)
    requires 4 <= i <= j
    ensures fib4_func(i) <= fib4_func(j)
    decreases j - i
{
    if i < j {
        lemma_fib4_nondecreasing_from_4(j);
        lemma_fib4_monotonic_from_4(i, j - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn fib4(n: i8) -> (result: i8)
    requires n >= 0
    ensures 
        result as int == fib4_func(n as int) &&
        (n == 0 ==> result == 0) &&
        (n == 1 ==> result == 0) &&
        (n == 2 ==> result == 2) &&
        (n == 3 ==> result == 0) &&
        (n >= 4 ==> result as int == fib4_func(n as int - 1) + fib4_func(n as int - 2) + fib4_func(n as int - 3) + fib4_func(n as int - 4))
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 0;
    }
    if n == 2 {
        return 2;
    }
    if n == 3 {
        return 0;
    }

    // n >= 4
    let mut a: i8 = 0; // fib4_func(0)
    let mut b: i8 = 0; // fib4_func(1)
    let mut c: i8 = 2; // fib4_func(2)
    let mut d: i8 = 0; // fib4_func(3)

    let mut i: i8 = 4;

    while i <= n
        invariant
            n >= 4,
            4 <= i <= n + 1,
            a as int == fib4_func(i as int - 4),
            b as int == fib4_func(i as int - 3),
            c as int == fib4_func(i as int - 2),
            d as int == fib4_func(i as int - 1),
            fib4_func(n as int) <= 127,
            fib4_func(n as int) >= 0,
        decreases n - i
    {
        proof {
            lemma_fib4_monotonic_from_4(i as int, n as int);
            lemma_fib4_nonnegative(i as int);
        }

        let next = a + b + c + d;
        
        a = b;
        b = c;
        c = d;
        d = next;
        
        i = i + 1;
    }

    return d;
}
// </vc-code>


}

fn main() {}