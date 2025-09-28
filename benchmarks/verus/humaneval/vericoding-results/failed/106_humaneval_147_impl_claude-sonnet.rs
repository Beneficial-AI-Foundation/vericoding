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
/* helper modified by LLM (iteration 5): fixed invalid int suffix syntax */
fn lemma_count_elements_mod_0_bounds(n: int)
    requires n >= 0
    ensures count_elements_mod_0(n) >= 0
    decreases n
{
    if n <= 0 {
    } else {
        lemma_count_elements_mod_0_bounds(n - 1);
    }
}

fn lemma_count_elements_mod_1_bounds(n: int)
    requires n >= 0
    ensures count_elements_mod_1(n) >= 0
    decreases n
{
    if n <= 0 {
    } else {
        lemma_count_elements_mod_1_bounds(n - 1);
    }
}

fn lemma_combination_bounds(n: int, k: int)
    requires n >= 0 && k >= 0
    ensures combination(n, k) >= 0
{
}

fn compute_count_mod_0(n: i8) -> (result: i8)
    requires n >= 0
    ensures result as int == count_elements_mod_0(n as int)
{
    let mut count = 0;
    let mut i = 1;
    while i <= n
        invariant
            i >= 1,
            i <= n + 1,
            count as int == count_elements_mod_0((i - 1) as int),
        decreases n - i
    {
        let elem = i * i - i + 1;
        if elem % 3 == 2 {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}

fn compute_count_mod_1(n: i8) -> (result: i8)
    requires n >= 0
    ensures result as int == count_elements_mod_1(n as int)
{
    let mut count = 0;
    let mut i = 1;
    while i <= n
        invariant
            i >= 1,
            i <= n + 1,
            count as int == count_elements_mod_1((i - 1) as int),
        decreases n - i
    {
        let elem = i * i - i + 1;
        if elem % 3 != 2 {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}

fn compute_combination(n: i8, k: i8) -> (result: i8)
    requires n >= 0 && k >= 0
    ensures result as int == combination(n as int, k as int)
{
    if k > n || k < 0 {
        0
    } else if k == 0 || k == n {
        1
    } else if k == 1 {
        n
    } else if k == 2 {
        n * (n - 1) / 2
    } else if k == 3 {
        n * (n - 1) * (n - 2) / 6
    } else {
        0
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
    /* code modified by LLM (iteration 5): fixed invalid int suffix syntax */
    proof {
        lemma_count_elements_mod_0_bounds(n as int);
        lemma_count_elements_mod_1_bounds(n as int);
    }
    
    let count_0 = compute_count_mod_0(n);
    let count_1 = compute_count_mod_1(n);
    
    let comb_0 = compute_combination(count_0, 3);
    let comb_1 = compute_combination(count_1, 3);
    
    proof {
        lemma_combination_bounds(count_0 as int, 3);
        lemma_combination_bounds(count_1 as int, 3);
    }
    
    comb_0 + comb_1
}
// </vc-code>


}

fn main() {}