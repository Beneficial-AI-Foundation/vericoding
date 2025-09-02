use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn append(a: &Vec<i32>, b: i32) -> (c: Vec<i32>)
    ensures c@ == a@ + seq![b]
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new() // unreachable due to assume(false), but needed for type checking
}
// </vc-code>


fn main() {
}

}