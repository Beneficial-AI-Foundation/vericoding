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
    if x < 18 {
        // Following original: a = 2*x, b = 4*x, result = (a+b)/2 = 6*x/2 = 3*x
        let a = 2 * x;
        let b = 4 * x; 
        let result = (a + b) / 2;
        
        proof {
            assert(a as int == 2 * (x as int));
            assert(b as int == 4 * (x as int));
            assert((a + b) as int == 6 * (x as int));
            assert(result as int == 3 * (x as int));
            lemma_three_times_div(x as int);
        }
        
        result
    } else {
        // Following original: y = 2*x, result = x + y = 3*x
        let y = 2 * x;
        let result = x + y;
        
        proof {
            assert(y as int == 2 * (x as int));
            assert(result as int == 3 * (x as int));
            lemma_three_times_div(x as int);
        }
        
        result
    }
}

fn main() {
}

}