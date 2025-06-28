use builtin::*;
use builtin_macros::*;

verus! {

spec fn Double(val: int) -> int {
    val * 2
}

fn main() {
}

fn TestDouble(val: int) -> (val2: int)
    ensures
        val2 == Double(val)
{
    val * 2
}

}