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
    let result = val * 2;
    assert(result == Double(val)); // proof that result equals Double(val)
    result
}

}