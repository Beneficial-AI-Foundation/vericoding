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
proof fn lemma_collatz_even_odd_result(even: u8)
    requires even > 0 && even % 2 == 0,
    ensures (iterate_to_odd(even as nat) as u8) <= 127,
{
    lemma_iterate_odd_decreases(even as nat);
    assert((iterate_to_odd(even as nat) as u8) <= 127) by {
        reveal_with_fuel(iterate_to_odd, 10);
    };
}

proof fn lemma_collatz_odd_result(odd: u8)
    requires odd > 0 && odd % 2 == 1,
    ensures next_odd_collatz(odd as nat) as u8 <= 127,
{
    let triple = 3 * odd as nat + 1;
    assert(triple % 2 == 0);
    lemma_iterate_odd_decreases(triple);
    assert((iterate_to_odd(triple) as u8) <= 127) by {
        reveal_with_fuel(iterate_to_odd, 10);
    };
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
    /* code modified by LLM (iteration 5): Fixed proof function calls and type safety */
    if n % 2 == 0 {
        lemma_collatz_even_odd_result(n);
        let mut current: u8 = n;
        while current % 2 == 0
            invariant
                current > 0,
                current <= n,
            decreases current,
        {
            current = (current / 2) as u8;
        }
        current
    } else {
        lemma_collatz_odd_result(n);
        let triple: u16 = (3 * n as u16) + 1;
        let mut current: u16 = triple;
        while current % 2 == 0
            invariant
                current >= 1,
                current <= triple,
            decreases current,
        {
            current = current / 2;
        }
        assert(current <= 127);
        current as u8
    }
}
// </vc-code>


}

fn main() {}