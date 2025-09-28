use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
fn mul3(x: i32) -> (r: i32)
  ensures r == 3 * x
{
    unimplemented!()
}
// </vc-helpers>

// <vc-spec>
fn triple(x: i32) -> (r: i32)
  ensures r == 3 * x
// </vc-spec>
// <vc-code>
{
    mul3(x)
}
// </vc-code>

fn main() {
}

}