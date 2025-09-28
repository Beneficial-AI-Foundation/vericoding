use vstd::prelude::*;

verus! {

// <vc-helpers>
// empty
// </vc-helpers>

// <vc-spec>
fn rotate_left_bits(n: u32, d: int) -> (result: u32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
// </vc-spec>
// <vc-code>
{
  let left_shift = d.try_as_u32().unwrap();
  let right_shift = 32u32 - left_shift;
  let n_left = n << left_shift;
  let n_right = n >> right_shift;
  let result = n_left | n_right;
  result
}
// </vc-code>

fn main() {
}

}