use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Triple(x: int) -> int
{
    3 * x
}

}