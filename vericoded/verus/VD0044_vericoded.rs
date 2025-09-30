use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn append(a: &Vec<i32>, b: i32) -> (c: Vec<i32>)
    ensures c@ == a@ + seq![b]
// </vc-spec>
// <vc-code>
{
    let mut c = a.clone();
    c.push(b);
    c
}
// </vc-code>

fn main() {
}

}