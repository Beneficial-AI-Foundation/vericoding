use vstd::prelude::*;

verus! {

spec fn factorial(n: int) -> int
    recommends n >= 0
    decreases n when n >= 0
{
    if n == 0 { 1 } else { n * factorial((n - 1) as int) }
}

// <vc-helpers>
proof fn lemma_factorial_step(n: int)
    requires
        n >= 1,
    ensures
        factorial(n) == n * factorial(n - 1),
{
    assert(n != 0);
    assert(factorial(n) == if n == 0 { 1 } else { n * factorial((n - 1) as int) });
    assert(((n - 1) as int) == n - 1);
}

proof fn lemma_factorial_0()
    ensures factorial(0) == 1,
{
    assert(factorial(0) == 1);
}

proof fn lemma_factorial_1()
    ensures factorial(1) == 1,
{
    lemma_factorial_0();
    lemma_factorial_step(1);
    assert(factorial(1) == 1 * factorial(0));
    assert(factorial(0) == 1);
}

proof fn lemma_factorial_2()
    ensures factorial(2) == 2,
{
    lemma_factorial_1();
    lemma_factorial_step(2);
    assert(factorial(2) == 2 * factorial(1));
    assert(factorial(1) == 1);
}

proof fn lemma_factorial_3()
    ensures factorial(3) == 6,
{
    lemma_factorial_2();
    lemma_factorial_step(3);
    assert(factorial(3) == 3 * factorial(2));
    assert(factorial(2) == 2);
    assert(3 * 2 == 6);
}

proof fn lemma_factorial_4()
    ensures factorial(4) == 24,
{
    lemma_factorial_3();
    lemma_factorial_step(4);
    assert(factorial(4) == 4 * factorial(3));
    assert(factorial(3) == 6);
    assert(4 * 6 == 24);
}

proof fn lemma_factorial_5()
    ensures factorial(5) == 120,
{
    lemma_factorial_4();
    lemma_factorial_step(5);
    assert(factorial(5) == 5 * factorial(4));
    assert(factorial(4) == 24);
    assert(5 * 24 == 120);
}

proof fn lemma_factorial_6()
    ensures factorial(6) == 720,
{
    lemma_factorial_5();
    lemma_factorial_step(6);
    assert(factorial(6) == 6 * factorial(5));
    assert(factorial(5) == 120);
    assert(6 * 120 == 720);
}

proof fn lemma_factorial_7()
    ensures factorial(7) == 5040,
{
    lemma_factorial_6();
    lemma_factorial_step(7);
    assert(factorial(7) == 7 * factorial(6));
    assert(factorial(6) == 720);
    assert(7 * 720 == 5040);
}

proof fn lemma_factorial_8()
    ensures factorial(8) == 40320,
{
    lemma_factorial_7();
    lemma_factorial_step(8);
    assert(factorial(8) == 8 * factorial(7));
    assert(factorial(7) == 5040);
    assert(8 * 5040 == 40320);
}

proof fn lemma_factorial_9()
    ensures factorial(9) == 362880,
{
    lemma_factorial_8();
    lemma_factorial_step(9);
    assert(factorial(9) == 9 * factorial(8));
    assert(factorial(8) == 40320);
    assert(9 * 40320 == 362880);
}
// </vc-helpers>

// <vc-spec>
fn factorial_of_last_digit(n: u64) -> (fact: u64)
    requires n >= 0
    ensures fact == factorial((n % 10) as int)
// </vc-spec>
// <vc-code>
{
    let d: u64 = n % 10;
    proof {
        assert(((n % 10) as int) == (d as int));
    }
    if d == 0 {
        proof { lemma_factorial_0(); }
        1u64
    } else if d == 1 {
        proof { lemma_factorial_1(); }
        1u64
    } else if d == 2 {
        proof { lemma_factorial_2(); }
        2u64
    } else if d == 3 {
        proof { lemma_factorial_3(); }
        6u64
    } else if d == 4 {
        proof { lemma_factorial_4(); }
        24u64
    } else if d == 5 {
        proof { lemma_factorial_5(); }
        120u64
    } else if d == 6 {
        proof { lemma_factorial_6(); }
        720u64
    } else if d == 7 {
        proof { lemma_factorial_7(); }
        5040u64
    } else if d == 8 {
        proof { lemma_factorial_8(); }
        40320u64
    } else {
        proof { 
            assert(d == 9);
            lemma_factorial_9(); 
        }
        362880u64
    }
}
// </vc-code>

fn main() {
}

}