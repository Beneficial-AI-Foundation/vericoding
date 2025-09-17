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
// </vc-helpers>

// <vc-spec>
fn get_max_triples(n: int) -> (result: int)
  requires
      valid_input(n),
  ensures
      result >= 0,
      result == count_valid_triples(n),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}