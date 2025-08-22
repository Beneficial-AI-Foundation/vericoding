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
}

proof fn lemma_three_times_div(x: int)
    ensures 
        (3 * x) / 3 == x,
        ((3 * x) / 3) * 3 == 3 * x
{
    assert((3 * x) % 3 == 0);
    lemma_div_mul_cancel(3 * x);
}

fn triple(x: i32) -> (result: i32)
    requires 
        triple_precond(x as int),
        -1000000 <= x <= 1000000
    ensures triple_postcond(x as int, result as int)
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn main() {
    // TODO: Remove this comment and implement the function body
}

}