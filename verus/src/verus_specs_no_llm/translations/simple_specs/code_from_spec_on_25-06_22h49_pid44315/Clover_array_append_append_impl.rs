use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn append(a: Vec<int>, b: int) -> (c: Vec<int>)
    ensures
        a@ + seq![b] == c@
{
    let a_view = a@;
    let mut result = a;
    result.push(b);
    assert(result@ == a_view + seq![b]);
    result
}

}