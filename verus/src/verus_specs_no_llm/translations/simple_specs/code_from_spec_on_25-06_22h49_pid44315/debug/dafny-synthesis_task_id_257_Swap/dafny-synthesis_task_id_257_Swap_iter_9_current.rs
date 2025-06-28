use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Swap(a: int, b: int) -> (result: Seq<int>)
    ensures
        result.len() == 2,
        result[0] == b,
        result[1] == a
{
    let result = seq![b, a];
    result
}

}