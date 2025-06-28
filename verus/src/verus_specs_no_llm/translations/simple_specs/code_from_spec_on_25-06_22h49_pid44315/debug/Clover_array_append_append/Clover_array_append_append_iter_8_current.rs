use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn append(a: Vec<int>, b: int) -> (c: Vec<int>)
    ensures
        a@ + seq![b] == c@
{
    let old_a = a@;
    let mut result = a;
    result.push(b);
    assert(old_a + seq![b] == result@);
    result
}

}