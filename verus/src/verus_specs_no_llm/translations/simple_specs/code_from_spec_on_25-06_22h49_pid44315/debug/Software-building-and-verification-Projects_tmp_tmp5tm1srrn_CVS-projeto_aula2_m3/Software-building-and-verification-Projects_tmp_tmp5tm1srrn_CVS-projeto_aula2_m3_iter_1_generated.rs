use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn m3(x: int, y: int) -> (z: bool)
    ensures
        z ==> x==y
{
    x == y
}

}