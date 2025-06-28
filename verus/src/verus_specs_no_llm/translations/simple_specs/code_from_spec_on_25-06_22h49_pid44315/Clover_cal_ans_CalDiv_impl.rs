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
    let x: int = 27;  // 191 / 7 = 27 (integer division)
    let y: int = 2;   // 191 % 7 = 2 (remainder)
    
    // Verus can verify these arithmetic facts automatically
    assert(191 / 7 == 27);
    assert(191 % 7 == 2);
    
    (x, y)
}

}