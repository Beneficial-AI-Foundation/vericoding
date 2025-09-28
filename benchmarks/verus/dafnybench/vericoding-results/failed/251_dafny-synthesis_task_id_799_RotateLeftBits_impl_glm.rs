use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn rotate_left_bits(n: u32, d: int) -> (result: u32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
// </vc-spec>
// <vc-code>
{
  let d_u32 = d as u32;
  let left = n << d_u32;
  let right = if d == 0 {
    0
  } else {
    n >> (32u32 - d_u32)
  };
  left | right
}
// </vc-code>

fn main() {
}

}