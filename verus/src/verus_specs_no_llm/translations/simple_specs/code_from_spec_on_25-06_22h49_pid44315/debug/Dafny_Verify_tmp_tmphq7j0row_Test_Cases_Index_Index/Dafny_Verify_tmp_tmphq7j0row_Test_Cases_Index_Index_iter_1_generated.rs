use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Index(n: int) -> (i: int)
    requires
        1 <= n
    ensures
        0 <= i < n
{
    0
}

}