// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn tri(n: nat) -> nat
  decreases if n % 2 == 0 { 0 } else { n }
{
  if n == 1 { 3 }
  else if n % 2 == 0 { 1 + n / 2 }
  else { tri((n - 1) as nat) + tri((n - 2) as nat) + tri(n + 1) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn tribonacci(n: nat) -> (result: Vec<nat>)
  ensures 
    result.len() == n + 1 &&
    (forall|i: int| 0 <= i <= n ==> result[i] == tri(i as nat))
// </vc-spec>
// <vc-code>
{
  assume(false);
  Vec::new()
}
// </vc-code>


}

fn main() {}