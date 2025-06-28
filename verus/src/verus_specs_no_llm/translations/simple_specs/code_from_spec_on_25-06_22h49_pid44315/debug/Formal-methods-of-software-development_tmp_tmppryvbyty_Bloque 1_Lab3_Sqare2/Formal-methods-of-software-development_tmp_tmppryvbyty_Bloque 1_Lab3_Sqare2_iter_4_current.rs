use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Square2(a: i32) -> (x: i32)
    requires
        a >= 1,
    ensures
        x == a * a,
{
    a * a
}

}