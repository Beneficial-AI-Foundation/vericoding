use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn fact_spec(x: int) -> int
    decreases x
{
    if x <= 0 {
        1
    } else {
        x * fact_spec(x - 1)
    }
}

fn Fact(x: int) -> (y: int)
    requires
        x >= 0
    ensures
        y == fact_spec(x),
        y >= 1
    decreases x
{
    if x <= 0 {
        1
    } else {
        let prev = Fact(x - 1);
        x * prev
    }
}

}