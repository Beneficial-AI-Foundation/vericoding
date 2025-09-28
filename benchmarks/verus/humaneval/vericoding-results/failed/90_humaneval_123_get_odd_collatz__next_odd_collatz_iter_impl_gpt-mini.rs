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
/* helper modified by LLM (iteration 5): recursive division to odd for u16 with proof */
fn div_to_odd_u16(orig: u16) -> (res: u16)
    requires orig > 0,
    ensures
        (res as nat) % 2 == 1,
        res as nat == iterate_to_odd(orig as nat),
    decreases orig as nat
{
    if orig % 2 == 1 {
        orig
    } else {
        div_to_odd_u16(orig / 2)
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
/* code modified by LLM (iteration 5): compute res_u16 using div_to_odd_u16 and cast with verifier::truncate */
{
    let res_u16: u16 = if n % 2 == 0 {
        div_to_odd_u16(n as u16)
    } else {
        let arg: u16 = 3u16 * (n as u16) + 1u16;
        div_to_odd_u16(arg)
    };
    let next: u8 = #[verifier::truncate] (res_u16 as u8);
    proof {
        if n % 2 == 0 {
            assert(res_u16 as nat == iterate_to_odd(n as nat));
            assert(res_u16 as nat == next_odd_collatz(n as nat));
        } else {
            assert(res_u16 as nat == iterate_to_odd(3 * (n as nat) + 1));
            assert(res_u16 as nat == next_odd_collatz(n as nat));
        }
        assert((res_u16 as nat) % 2 == 1);
        assert((next as nat) % 2 == 1);
        assert(next as nat == res_u16 as nat);
    }
    next
}
// </vc-code>


}

fn main() {}