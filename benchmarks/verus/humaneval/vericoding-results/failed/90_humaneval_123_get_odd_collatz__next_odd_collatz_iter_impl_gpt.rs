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
proof fn lemma_iterate_to_odd_result_is_odd(n: nat)
    ensures
        n > 0 && n % 2 == 0 ==> iterate_to_odd(n) % 2 == 1,
    decreases n,
{
    if n > 0 && n % 2 == 0 {
        if (n / 2) % 2 == 1 {
            assert((n / 2) % 2 == 1);
        } else {
            lemma_iterate_to_odd_result_is_odd(n / 2);
            assert(iterate_to_odd(n / 2) % 2 == 1);
        }
    }
}

proof fn lemma_next_odd_collatz_is_odd(n: nat)
    ensures
        n > 0 ==> next_odd_collatz(n) % 2 == 1,
{
    if n > 0 {
        if n % 2 == 0 {
            lemma_iterate_to_odd_result_is_odd(n);
            assert(next_odd_collatz(n) == iterate_to_odd(n));
            assert(next_odd_collatz(n) % 2 == 1);
        } else {
            let m = 3 * n + 1;
            assert(m > 0);
            assert(m % 2 == 0);
            lemma_iterate_to_odd_result_is_odd(m);
            assert(next_odd_collatz(n) == iterate_to_odd(m));
            assert(next_odd_collatz(n) % 2 == 1);
        }
    }
}

fn iter_to_odd_u16(m: u16) -> (r: u16)
    requires
        m > 0,
    ensures
        (r as nat) % 2 == 1,
        (r as nat) == iterate_to_odd(m as nat),
        (r as nat) <= (m as nat),
    decreases m as int,
{
    if m % 2 == 0u16 {
        let half: u16 = m / 2u16;
        if half % 2 == 1u16 {
            half
        } else {
            let rr = iter_to_odd_u16(half);
            rr
        }
    } else {
        1u16
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
    proof { lemma_next_odd_collatz_is_odd(n as nat); }
    if n % 2 == 0u8 {
        let r16 = iter_to_odd_u16(n as u16);
        // r16 <= n <= 255, so this cast is safe
        assert((r16 as nat) <= (n as nat));
        let next_u8: u8 = r16 as u8;
        next_u8
    } else {
        // compute 3*n + 1 in a wider type to avoid overflow, then strip factors of 2
        let m16: u16 = (3u16 * (n as u16)) + 1u16;
        let r16 = iter_to_odd_u16(m16);
        let next_u8: u8 = r16 as u8;
        next_u8
    }
}
// </vc-code>


}

fn main() {}