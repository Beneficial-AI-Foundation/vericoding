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
/* helper modified by LLM (iteration 2): changed type from u8 to u32 to avoid arithmetic overflow */
fn iterate_to_odd_exec(n: u32) -> (res: u32)
    requires
        n > 0,
    ensures
        (res as nat) % 2 == 1,
        res as nat == iterate_to_odd(n as nat),
    decreases n,
{
    if n % 2 == 0 {
        if (n / 2) % 2 == 1 {
            n / 2
        } else {
            iterate_to_odd_exec(n / 2)
        }
    } else {
        1
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
/* code modified by LLM (iteration 2): used u32 to avoid overflow in calculation and cast back to u8 */
{
    let rn = n as u32;
    let res_u32 = if rn % 2 == 0 {
        iterate_to_odd_exec(rn)
    } else {
        iterate_to_odd_exec(3 * rn + 1)
    };
    res_u32 as u8
}
// </vc-code>


}

fn main() {}