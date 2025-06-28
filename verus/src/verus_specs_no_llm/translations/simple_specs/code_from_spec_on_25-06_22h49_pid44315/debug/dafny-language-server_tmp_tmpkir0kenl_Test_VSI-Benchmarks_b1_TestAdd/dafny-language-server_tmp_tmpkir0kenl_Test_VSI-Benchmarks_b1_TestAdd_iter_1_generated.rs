use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Add(x: int, y: int) -> (r: int)
    ensures r == x + y
{
    x + y
}

// Test method that calls Add and verifies the result
fn TestAdd(x: int, y: int) -> (r: int)
    ensures r == x + y
{
    let result = Add(x, y);
    result
}

}