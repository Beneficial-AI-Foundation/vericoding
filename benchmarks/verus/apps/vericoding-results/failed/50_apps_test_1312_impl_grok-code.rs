// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int) -> bool {
  n >= m > 0
}

spec fn sum(s: Seq<int>) -> int
  decreases s.len()
{
  if s.len() == 0 { 
    0int 
  } else { 
    s[0] + sum(s.subrange(1, s.len() as int)) 
  }
}

spec fn count(s: Seq<int>, val: int) -> int
  decreases s.len()
{
  if s.len() == 0 { 
    0int 
  } else { 
    (if s[0] == val { 1int } else { 0int }) + count(s.subrange(1, s.len() as int), val) 
  }
}

spec fn optimal_distribution(result: Seq<int>, n: int, m: int) -> bool {
  &&& m > 0
  &&& result.len() == m
  &&& (forall|i: int| 0 <= i < result.len() ==> result[i] > 0)
  &&& sum(result) == n
  &&& (forall|i: int| 0 <= i < result.len() ==> result[i] == n / m || result[i] == n / m + 1)
  &&& count(result, n / m) == m - (n % m)
  &&& count(result, n / m + 1) == n % m
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: Vec<i8>)
  requires valid_input(n as int, m as int)
  ensures optimal_distribution(result@.map(|i: int, x: i8| x as int), n as int, m as int)
// </vc-spec>
// <vc-code>
  /* code modified by LLM (iteration 5): Fixed compilation by simplifying casts, removed unnecessary rem_i8 and base_i8 variables, used base and rem directly for logic, and ensured consistent types in proofs */
{
    let base: int = n as int / m as int;
    let rem: int = n as int % m as int;
    let extra: i8 = (base + 1) as i8;
    let mut result: Vec<i8> = Vec::new();
    let ghost mut current_sum: int = 0;
    let ghost mut current_extra_count: int = 0;
    let mut i: usize = 0;
    while i < m as usize
        invariant
            i as int <= m as int,
            result@.len() == i as int,
            current_sum == sum(result@.map(|ii: int, x: i8| x as int)),
            current_extra_count == count(result@.map(|ii: int, x: i8| x as int), base + 1),
            forall |j: int| 0 <= j < i as int ==> result@[j] as int == if j < rem { (base + 1) } else { base }
        decreases m as int - i as int
    {
        if (i as int < rem) {
            result.push(extra);
            proof {
                current_sum = current_sum + (extra as int);
                current_extra_count = current_extra_count + 1;
            }
        } else {
            result.push(base as i8);
            proof {
                current_sum = current_sum + base;
            }
        }
        proof {
            assert(result@[i as int] as int == if i as int < rem { base + 1 } else { base });
            assert(current_sum == sum(result@.map(|ii: int, x: i8| x as int)));
            assert(current_extra_count == count(result@.map(|ii: int, x: i8| x as int), base + 1));
        }
        i = i + 1;
    }
    proof {
        assert(result@.len() == m as int);
        assert(sum(result@.map(|ii: int, x: i8| x as int)) == current_sum);
        assert(count(result@.map(|ii: int, x: i8| x as int), base + 1) == current_extra_count);
        assert(count(result@.map(|ii: int, x: i8| x as int), base) == m as int - current_extra_count);
        assert(forall |j: int| 0 <= j < result@.len() ==> result@[j] as int == if j < rem { base + 1 } else { base });
        assert(sum(result@.map(|ii: int, x: i8| x as int)) == n as int);
        assert(count(result@.map(|ii: int, x: i8| x as int), base == n as int / m as int));
        assert(count(result@.map(|ii: int, x: i8| x as int), base + 1) == n as int % m as int);
    }
    result
}

// </vc-code>


}

fn main() {}