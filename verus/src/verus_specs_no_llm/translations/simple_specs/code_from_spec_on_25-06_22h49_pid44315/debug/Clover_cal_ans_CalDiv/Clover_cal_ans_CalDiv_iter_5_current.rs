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
    
    // Verify our calculations
    assert(191 == 7 * 27 + 2);
    assert(x_val == 191/7);
    assert(y_val == 191%7);
    
    (x_val, y_val)
}

}