use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn triple(x: i32) -> (r: i32)
    ensures r == 3 * x
{
    3 * x
}

}