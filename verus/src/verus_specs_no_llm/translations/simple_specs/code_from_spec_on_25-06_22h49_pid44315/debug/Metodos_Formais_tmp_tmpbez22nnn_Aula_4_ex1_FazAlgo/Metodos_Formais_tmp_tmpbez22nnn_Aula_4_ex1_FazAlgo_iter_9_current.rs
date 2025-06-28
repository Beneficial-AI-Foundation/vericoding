use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Par(n: int) -> bool {
    n % 2 == 0
}

fn FazAlgo(a: i32, b: i32) -> (x: i32, y: i32)
    requires
        a >= b,
        Par((a - b) as int),
    ensures
        result.0 == (a - b) / 2 && result.1 == a + b
{
    let diff = a - b;
    let x = diff / 2;
    let y = a + b;
    
    (x, y)
}

}