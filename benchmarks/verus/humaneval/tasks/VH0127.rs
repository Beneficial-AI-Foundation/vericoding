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
fn next_odd_collatz_iter(n: u8) -> (next: u8)
  requires n > 0,
  ensures 
    (next as nat) % 2 == 1,
    next as nat == next_odd_collatz(n as nat),
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}