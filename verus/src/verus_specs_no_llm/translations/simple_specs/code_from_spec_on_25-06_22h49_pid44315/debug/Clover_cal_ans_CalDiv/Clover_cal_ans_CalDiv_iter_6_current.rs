use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CalDiv() -> (x: int, y: int)
    ensures
        x == 191/7,
        y == 191%7
{
    let x_val: int = 27;  // 191 / 7 = 27 (integer division)
    let y_val: int = 2;   // 191 % 7 = 2 (remainder)
    
    // Add proof that our hardcoded values are correct
    proof {
        assert(191 == 7 * 27 + 2) by(nonlinear_arith);
        assert(27 == 191/7) by(nonlinear_arith);
        assert(2 == 191%7) by(nonlinear_arith);
    }
    
    (x_val, y_val)
}

}