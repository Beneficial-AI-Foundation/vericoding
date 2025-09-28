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
/* helper modified by LLM (iteration 2): partition of counts and closed form for count_elements_mod_0 */
proof fn lemma_counts_partition(n: int)
    requires
        n >= 0,
    ensures
        count_elements_mod_0(n) >= 0,
        count_elements_mod_1(n) >= 0,
        count_elements_mod_0(n) + count_elements_mod_1(n) == n,
    decreases n
{
    if n <= 0 {
        assert(count_elements_mod_0(n) == 0);
        assert(count_elements_mod_1(n) == 0);
    } else {
        lemma_counts_partition(n - 1);
        if n % 3 == 2 {
            assert(count_elements_mod_0(n) == 1 + count_elements_mod_0(n - 1));
            assert(count_elements_mod_1(n) == count_elements_mod_1(n - 1));
        } else {
            assert(count_elements_mod_0(n) == count_elements_mod_0(n - 1));
            assert(count_elements_mod_1(n) == 1 + count_elements_mod_1(n - 1));
        }
        assert(count_elements_mod_0(n - 1) + count_elements_mod_1(n - 1) == n - 1);
        assert(count_elements_mod_0(n) + count_elements_mod_1(n)
            == count_elements_mod_0(n - 1) + count_elements_mod_1(n - 1) + 1);
        assert(count_elements_mod_0(n) + count_elements_mod_1(n) == n);
    }
}

/* helper modified by LLM (iteration 2): closed form (n+1)/3 for count_elements_mod_0 */
proof fn lemma_count0_closed_form(n: int)
    requires
        n >= 0,
    ensures
        count_elements_mod_0(n) == (n + 1) / 3,
    decreases n
{
    if n <= 0 {
        assert(count_elements_mod_0(n) == 0);
        assert((n + 1) / 3 == 0);
    } else {
        lemma_count0_closed_form(n - 1);
        if n % 3 == 2 {
            assert(count_elements_mod_0(n) == 1 + count_elements_mod_0(n - 1));
            assert(count_elements_mod_0(n - 1) == n / 3);
            assert((n + 1) / 3 == (n / 3) + 1);
            assert(count_elements_mod_0(n) == (n + 1) / 3);
        } else {
            assert(count_elements_mod_0(n) == count_elements_mod_0(n - 1));
            assert(count_elements_mod_0(n - 1) == n / 3);
            assert((n + 1) / 3 == n / 3);
            assert(count_elements_mod_0(n) == (n + 1) / 3);
        }
    }
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
    /* code modified by LLM (iteration 2): compute using machine ints; move 'int' usage into proof blocks */
    let n_i64: i64 = n as i64;
    let c0_i64: i64 = (n_i64 + 1) / 3;
    let c1_i64: i64 = n_i64 - c0_i64;
    let t0_i64: i64 = (c0_i64 * (c0_i64 - 1) * (c0_i64 - 2)) / 6;
    let t1_i64: i64 = (c1_i64 * (c1_i64 - 1) * (c1_i64 - 2)) / 6;
    let tot_i64: i64 = t0_i64 + t1_i64;
    proof {
        let ni: int = n as int;
        assert(valid_input(ni));
        lemma_counts_partition(ni);
        lemma_count0_closed_form(ni);
    }
    let result: i8 = tot_i64 as i8;
    result
}
// </vc-code>


}

fn main() {}