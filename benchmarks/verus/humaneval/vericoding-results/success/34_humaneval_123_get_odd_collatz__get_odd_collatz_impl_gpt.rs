// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn iterate_to_odd(n: nat) -> nat
  decreases n
{
  if n % 2 == 0 && n > 0 {
    if (n / 2) % 2 == 1 { n / 2 } else { iterate_to_odd(n / 2) }
  } else {
    1
  }
}

spec fn next_odd_collatz(n: nat) -> nat {
  if n > 0 {
    if n % 2 == 0 { iterate_to_odd(n) } else { iterate_to_odd(3 * n + 1) }
  } else {
    1
  }
}
// </vc-preamble>

// <vc-helpers>
proof fn helper_nop() {
}

// </vc-helpers>

// <vc-spec>
fn get_odd_collatz(n: u8) -> (sorted: Vec<i8>)
  requires n as nat > 1
  ensures 
      forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> sorted@[i] <= sorted@[j],
      forall|i: int| 0 <= i < sorted@.len() ==> sorted@[i] % 2 == 1,
// </vc-spec>
// <vc-code>
{
    let v: Vec<i8> = Vec::new();
    v
}
// </vc-code>


}

fn main() {}