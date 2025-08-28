use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn append(a: &Vec<i32>, b: i32) -> (c: Vec<i32>)
    ensures c@ == a@ + seq![b]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result = a.clone();
    result.push(b);
    result
}
// </vc-code>

fn main() {
}

}