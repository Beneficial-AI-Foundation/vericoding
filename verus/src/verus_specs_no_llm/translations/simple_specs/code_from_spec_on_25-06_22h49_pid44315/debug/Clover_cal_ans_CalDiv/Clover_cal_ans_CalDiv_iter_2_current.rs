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
    (27, 2)
}

}