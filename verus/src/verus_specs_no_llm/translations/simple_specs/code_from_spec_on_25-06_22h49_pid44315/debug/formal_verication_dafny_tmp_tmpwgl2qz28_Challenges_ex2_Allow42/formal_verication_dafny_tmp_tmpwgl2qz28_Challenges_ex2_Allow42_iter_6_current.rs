use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Allow42(x: int, y: int) -> (z: int, err: bool)
    ensures
        y != 42 ==> z == x/(42-y) && err == false,
        y == 42 ==> z == 0 && err == true
{
    if y == 42 {
        (0, true)
    } else {
        let divisor = 42 - y;
        
        // Prove that divisor != 0 when y != 42
        assert(divisor != 0) by {
            if divisor == 0 {
                assert(42 - y == 0);
                assert(y == 42);
                // This contradicts our condition y != 42
                assert(false);
            }
        };
        
        let quotient = x / divisor;
        (quotient, false)
    }
}

}