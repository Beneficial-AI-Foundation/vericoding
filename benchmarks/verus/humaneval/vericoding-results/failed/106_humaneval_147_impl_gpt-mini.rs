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
/* helper modified by LLM (iteration 2): fixed return signature and ensures names */
fn iter_count_mods(n: int) -> (int, int)
    requires
        n >= 0,
    ensures
        result.0 == count_elements_mod_0(n),
        result.1 == count_elements_mod_1(n),
{
    let mut i: int = 1;
    let mut c0_mut: int = 0;
    let mut c1_mut: int = 0;
    while i <= n
        invariant
            1 <= i <= n + 1,
            c0_mut + c1_mut == i - 1,
            c0_mut == count_elements_mod_0(i - 1),
            c1_mut == count_elements_mod_1(i - 1),
        decreases n - (i - 1)
    {
        if i % 3 == 2 {
            c0_mut = c0_mut + 1;
            proof {
                assert(c0_mut == 1 + count_elements_mod_0(i - 1));
                assert(count_elements_mod_0(i) == 1 + count_elements_mod_0(i - 1));
                assert(c0_mut == count_elements_mod_0(i));
            }
        } else {
            c1_mut = c1_mut + 1;
            proof {
                assert(c1_mut == 1 + count_elements_mod_1(i - 1));
                assert(count_elements_mod_1(i) == 1 + count_elements_mod_1(i - 1));
                assert(c1_mut == count_elements_mod_1(i));
            }
        }
        i = i + 1;
    }
    (c0_mut, c1_mut)
}

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
    /* code modified by LLM (iteration 2): compute counts and convert to i8 */
    let n_int: int = n as int;
    let (c0, c1) = iter_count_mods(n_int);
    let total: int = combination(c0, 3) + combination(c1, 3);
    let result_i8: i8 = total as i8;
    proof {
        assert(total == count_valid_triples(n_int));
        assert(result_i8 as int == total);
    }
    result_i8
}

// </vc-code>


}

fn main() {}