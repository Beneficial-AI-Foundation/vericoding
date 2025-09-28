// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn array_element(i: int) -> int
  recommends i >= 1
{
  i * i - i + 1
}

spec fn count_elements_mod_0(n: int) -> int
  recommends n >= 0
  decreases n when n >= 0
{
  if n <= 0 { 0 }
  else if n % 3 == 2 { 1 + count_elements_mod_0(n - 1) }
  else { count_elements_mod_0(n - 1) }
}

spec fn count_elements_mod_1(n: int) -> int
  recommends n >= 0
  decreases n when n >= 0
{
  if n <= 0 { 0 }
  else if n % 3 != 2 { 1 + count_elements_mod_1(n - 1) }
  else { count_elements_mod_1(n - 1) }
}

spec fn combination(n: int, k: int) -> int
  recommends n >= 0 && k >= 0
{
  if k > n || k < 0 { 0 }
  else if k == 0 || k == n { 1 }
  else if k == 1 { n }
  else if k == 2 { n * (n - 1) / 2 }
  else if k == 3 { n * (n - 1) * (n - 2) / 6 }
  else { 0 }
}

spec fn count_valid_triples(n: int) -> int
  recommends n >= 1
{
  let count_0 = count_elements_mod_0(n);
  let count_1 = count_elements_mod_1(n);
  combination(count_0, 3) + combination(count_1, 3)
}

spec fn valid_input(n: int) -> bool
{
  n >= 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [removed] */
// </vc-helpers>

// <vc-spec>
fn get_max_triples(n: i8) -> (result: i8)
  requires
      valid_input(n as int),
  ensures
      result >= 0,
      result as int == count_valid_triples(n as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected type of loop counter `i` to `int` for modulo operation. */
    let n_int: Ghost<int> = Ghost(n as int);
    let mut count_0: i8 = 0;
    let mut count_1: i8 = 0;
    let mut i: int = 1; // Changed i to int

    while (i <= n as int)
        invariant
            i >= 1,
            i <= n as int + 1,
            count_0 as int == count_elements_mod_0(i - 1),
            count_1 as int == count_elements_mod_1(i - 1),
            n_int@ == n as int,
        decreases (n as int - i) as int
    {
        proof {
            assert((i as int) % 3 == 2 || (i as int) % 3 != 2);
        }
        if (i % 3 == 2) {
            count_0 = count_0 + 1;
        } else {
            count_1 = count_1 + 1;
        }
        i = i + 1;
    }

    proof {
        assert(count_0 as int == count_elements_mod_0(n as int));
        assert(count_1 as int == count_elements_mod_1(n as int));
    }

    let comb_0_3_ghost: Ghost<int>;
    let comb_1_3_ghost: Ghost<int>;

    proof {
        comb_0_3_ghost = Ghost(combination(count_0 as int, 3));
        comb_1_3_ghost = Ghost(combination(count_1 as int, 3));
    }

    ( (comb_0_3_ghost@ + comb_1_3_ghost@) as i8 )
}
// </vc-code>


}

fn main() {}