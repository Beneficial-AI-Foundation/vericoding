use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn StarNumber(n: int) -> (star: int)
    requires
        n >= 0
    ensures
        star == 6 * n * (n - 1) + 1
{
    let result = 6 * n * (n - 1) + 1;
    assert(result == 6 * n * (n - 1) + 1);
    result
}

}