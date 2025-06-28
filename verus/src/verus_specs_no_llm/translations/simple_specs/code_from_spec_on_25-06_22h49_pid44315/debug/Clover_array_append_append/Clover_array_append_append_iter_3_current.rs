use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn append(a: Vec<int>, b: int) -> (c: Vec<int>)
    ensures
        a@ + [b] == c@
{
    let mut result = a;
    result.push(b);
    result
}

}