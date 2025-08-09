use vstd::prelude::*;

verus! {

spec fn triple_precond(x: int) -> bool {
    true
}

spec fn triple_postcond(x: int, result: int) -> bool {
    result / 3 == x && (result / 3) * 3 == result
}

proof fn lemma_div_mul_cancel(n: int)
    requires n % 3 == 0
    ensures n / 3 * 3 == n
{
    // This is a fundamental property of division and multiplication
    // When n is divisible by 3, (n / 3) * 3 == n
}

proof fn lemma_three_times_div(x: int)
    ensures 
        (3 * x) / 3 == x,
        ((3 * x) / 3) * 3 == 3 * x
{
    // (3 * x) / 3 == x by definition of division
    // ((3 * x) / 3) * 3 == x * 3 == 3 * x
}

fn triple(x: i32) -> (result: i32)
    requires 
        triple_precond(x as int),
        -1000000 <= x <= 1000000
    ensures triple_postcond(x as int, result as int)
{
    proof {
        lemma_three_times_div(x as int);
    }
    3 * x
}

fn main() {
    let result = triple(5);
    assert(result == 15);
}

}