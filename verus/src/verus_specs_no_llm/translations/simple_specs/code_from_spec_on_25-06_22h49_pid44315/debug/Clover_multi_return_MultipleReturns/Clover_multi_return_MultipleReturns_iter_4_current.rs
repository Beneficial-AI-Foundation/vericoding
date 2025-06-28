use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MultipleReturns(x: int, y: int) -> (more: int, less: int)
    ensures
        more == x + y,
        less == x - y
{
    let result_more = x + y;
    let result_less = x - y;
    (result_more, result_less)
}

}