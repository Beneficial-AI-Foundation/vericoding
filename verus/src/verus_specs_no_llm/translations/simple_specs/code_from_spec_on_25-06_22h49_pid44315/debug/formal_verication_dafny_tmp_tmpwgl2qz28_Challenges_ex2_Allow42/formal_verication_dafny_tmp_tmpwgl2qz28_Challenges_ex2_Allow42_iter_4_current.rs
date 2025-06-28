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
        // Proof that divisor != 0 when y != 42
        assert(y != 42);
        assert(divisor == 42 - y);
        assert(divisor != 0) by {
            // If divisor == 0, then 42 - y == 0, which means y == 42
            // But we know y != 42, so divisor != 0
            if divisor == 0 {
                assert(42 - y == 0);
                assert(y == 42);
                assert(false); // contradiction
            }
        };
        let quotient = x / divisor;
        (quotient, false)
    }
}

}