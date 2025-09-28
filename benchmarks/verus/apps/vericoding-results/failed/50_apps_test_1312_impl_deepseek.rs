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
/* helper modified by LLM (iteration 5): Fixed compilation error and verified base quotient computation */
fn compute_base_quotient(n: int, m: int) -> (base: int, remainder: int)
    requires
        n >= m > 0,
    ensures
        base == n / m,
        remainder == n % m,
{
    let base = n / m;
    let remainder = n % m;
    (base, remainder)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: Vec<i8>)
  requires valid_input(n as int, m as int)
  ensures optimal_distribution(result@.map(|i: int, x: i8| x as int), n as int, m as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed syntax error with division operator */
{
    let n_int = n as int;
    let m_int = m as int;
    
    let mut result: Vec<i8> = Vec::new();
    let (base, remainder) = compute_base_quotient(n_int, m_int);
    let base_val = base as i8;
    let remainder_val = remainder as usize;
    
    let mut i: usize = 0;
    while i < m_int as usize
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] as int == base || result@[j] as int == base + 1,
            sum(result@.map(|index: int, x: i8| x as int)) <= n_int,
    {
        if i < remainder_val {
            result.push((base + 1) as i8);
        } else {
            result.push(base as i8);
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}