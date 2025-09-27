// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn mod_value() -> nat { 1000000000 }

fn compute_steady_tables(n: usize, m: usize) -> (result: usize)
    requires 
        n > 0,
        m > 0,
    ensures 
        result < mod_value(),
        result >= n,
        result >= m,
        (n == 1 && m == 1) ==> result == 2,
        n > 0 ==> result >= n * n,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {
    // let result1 = compute_steady_tables(1, 1);
    // println!("{}", result1);
    
    // let result2 = compute_steady_tables(2, 2);
    // println!("{}", result2);
    
    // let result3 = compute_steady_tables(2, 3);
    // println!("{}", result3);
}