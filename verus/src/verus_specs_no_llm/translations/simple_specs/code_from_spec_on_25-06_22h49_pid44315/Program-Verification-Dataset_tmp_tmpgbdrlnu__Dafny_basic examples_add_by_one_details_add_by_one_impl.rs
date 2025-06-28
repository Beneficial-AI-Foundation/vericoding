use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn add_by_one(x: int, y: int) -> (r: int)
    ensures r == x + y + 1
{
    x + y + 1
}

}