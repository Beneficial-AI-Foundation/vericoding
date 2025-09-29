// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn iterate_to_odd(n: nat) -> nat
  decreases n,
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

// </vc-helpers>

// <vc-spec>
fn get_odd_collatz_unsorted(n: u8) -> (odd_collatz: Vec<u8>)
  requires n as nat > 1,
  ensures 
    forall|i: int| 0 <= i < odd_collatz@.len() ==> #[trigger] odd_collatz@[i] as nat % 2 == 1,
    forall|i: int| 1 <= i < odd_collatz@.len() ==> #[trigger] odd_collatz@[i] as nat == next_odd_collatz(odd_collatz@[i - 1] as nat),
// </vc-spec>
// <vc-code>
{
    let v: Vec<u8> = Vec::new();
    v
}
// </vc-code>


}

fn main() {}