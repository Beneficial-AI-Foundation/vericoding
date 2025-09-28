// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n > 0
}

spec fn fib_spec(n: int) -> int
    decreases n
{
    if n <= 0 { 1 }
    else if n == 1 { 1 }
    else if n == 2 { 1 }
    else { fib_spec(n - 1) + fib_spec(n - 2) }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_fib_step(k: int)
    requires
        k >= 1,
    ensures
        fib_spec(k + 2) == fib_spec(k + 1) + fib_spec(k),
{
    reveal(fib_spec);
}

/* helper modified by LLM (iteration 4): added reveal(fib_spec) to allow unfolding of the definition */
proof fn lemma_fib_positive(k: int)
    requires
        k >= 1,
    ensures
        fib_spec(k) > 0,
    decreases k,
{
    reveal(fib_spec);
    if k > 2 {
        lemma_fib_positive(k - 1);
        lemma_fib_positive(k - 2);
        assert(fib_spec(k) == fib_spec(k - 1) + fib_spec(k - 2));
    }
}
// </vc-helpers>

// <vc-spec>
fn fib(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures 
        result as int == fib_spec(n as int) &&
        result > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): use i32 for calculations to prevent overflow */
{
    if n == 1i8 {
        return 1i8;
    }
    if n == 2i8 {
        return 1i8;
    }

    let mut a: i32 = 1;
    let mut b: i32 = 1;
    let mut i: i8 = 2;

    while i < n
        invariant
            2 <= i <= n,
            a as int == fib_spec(i as int - 1),
            b as int == fib_spec(i as int),
        decreases n - i
    {
        proof {
            lemma_fib_step(i as int - 1);
        }
        
        let temp = a + b;
        a = b;
        b = temp;
        i = i + 1;
    }
    
    proof {
        lemma_fib_positive(n as int);
    }
    b as i8
}
// </vc-code>


}

fn main() {}