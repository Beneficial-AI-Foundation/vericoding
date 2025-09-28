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
spec fn is_odd(n: nat) -> bool {
    n % 2 == 1
}

spec fn halve_until_odd(n: nat) -> nat
  decreases n,
{
    if n % 2 == 0 && n > 0 {
        if is_odd(n / 2) { n / 2 } else { halve_until_odd(n / 2) }
    } else {
        n
    }
}

proof fn lemma_halve_until_odd_preserves_value(n: nat)
  ensures halve_until_odd(n) * (2^n) == n
  decreases n,
{
    if n % 2 == 0 && n > 0 {
        lemma_halve_until_odd_preserves_value(n / 2);
    } else {
        assert (2^0) == 1;
    }
}
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
    let n_nat = n as nat;
    let result = if n_nat % 2 == 0 {
        halve_until_odd(n_nat)
    } else {
        halve_until_odd(3 * n_nat + 1)
    };
    result as u8
}
// </vc-code>


}

fn main() {}