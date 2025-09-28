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
proof fn lemma_count_sum_is_total(k: int)
    requires k >= 0
    ensures
        count_elements_mod_0(k) >= 0,
        count_elements_mod_1(k) >= 0,
        count_elements_mod_0(k) + count_elements_mod_1(k) == k,
    decreases k
{
    if k > 0 {
        lemma_count_sum_is_total(k - 1);
    }
}

/* helper modified by LLM (iteration 2): fixed compilation errors by using a correct library lemma */
proof fn lemma_prod_3_consecutive_is_divisible_by_6(n: int)
    ensures
        (n * (n - 1) * (n - 2)) % 6 == 0,
{
    vstd::arithmetic::extra::lemma_factorial_divides_n_consecutive_integers(n - 2, 3);
    assert(vstd::arithmetic::extra::factorial(3) == 6);
}

fn comb3(n: i8) -> (result: i32)
    requires
        n >= 0,
    ensures
        result as int == combination(n as int, 3),
{
    if n < 3 {
        return 0;
    }
    let n_i32 = n as i32;
    proof {
        lemma_prod_3_consecutive_is_divisible_by_6(n_i32 as int);
    }
    n_i32 * (n_i32 - 1) * (n_i32 - 2) / 6
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
/* code modified by LLM (iteration 2): addressed compilation errors in helpers */
{
    let mut count_0: i8 = 0;
    let mut i: i8 = 1;
    while i <= n
        invariant
            n >= 1,
            1 <= i <= n + 1,
            count_0 >= 0,
            count_0 as int == count_elements_mod_0((i - 1) as int),
        decreases n - i
    {
        if i % 3 == 2 {
            count_0 = count_0 + 1;
        }
        i = i + 1;
    }

    let count_1 = n - count_0;
    proof {
        lemma_count_sum_is_total(n as int);
        assert(count_1 as int == count_elements_mod_1(n as int));
        assert(count_1 >= 0);
    }

    let comb_0 = comb3(count_0);
    let comb_1 = comb3(count_1);
    let total = comb_0 + comb_1;

    proof {
        assert(total as int == count_valid_triples(n as int));
    }

    total as i8
}
// </vc-code>


}

fn main() {}