use vstd::prelude::*;

verus! {

spec fn triple_precond(x: int) -> bool {
    true
}

spec fn triple_postcond(x: int, result: int) -> bool {
    result / 3 == x && result / 3 * 3 == result
}

fn triple(x: u32) -> (result: u32)
    requires 
        triple_precond(x as int),
        x <= u32::MAX / 3
    ensures 
        triple_postcond(x as int, result as int)
{
    if x == 0 {
        0
    } else {
        let result = 3 * x;
        
        proof {
            // Basic mathematical fact: for any integer n, (3 * n) / 3 = n
            let x_int = x as int;
            let result_int = result as int;
            
            assert(result_int == 3 * x_int);
            
            // Use the lemma that (a * b) / a = b when a != 0
            vstd::arithmetic::div_mod::lemma_div_multiples_vanish(3int, x_int);
            assert((3 * x_int) / 3int == x_int);
            assert(result_int / 3int == x_int);
            
            // And the reverse: result_int / 3 * 3 = result_int when result_int % 3 = 0
            assert((3 * x_int) % 3int == 0int);
            assert(result_int % 3int == 0int);
            assert(result_int / 3int * 3int == result_int);
        }
        
        result
    }
}

} // verus!

fn main() {}