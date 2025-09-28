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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: Vec<i8>)
  requires valid_input(n as int, m as int)
  ensures optimal_distribution(result@.map(|i: int, x: i8| x as int), n as int, m as int)
// </vc-spec>
// <vc-code>
{
        /* code modified by LLM (iteration 5): fixed compilation by converting ghost int types to usize in non-ghost loop conditions and using int in ghost invariants with proper casting */
        let base = n / m;
        let rem = n % m;

        let mut result = Vec::new();

        while result.len() < (rem as usize)
            invariant
                0 <= (result.len() as int) <= (rem as int),
                forall|k: int| 0 <= k < (result.len() as int) ==> result@[k] == (base as int + 1),
            decreases (rem as int) - (result.len() as int)
        {
            result.push((base + 1) as i8);
        }

        while result.len() < (m as usize)
            invariant
                (rem as int) <= (result.len() as int) <= (m as int),
                forall|i: int| 0 <= i < (rem as int) ==> result@[i] == (base as int + 1),
                forall|i: int| (rem as int) <= i < (result.len() as int) ==> result@[i] == base as int,
            decreases (m as int) - (result.len() as int)
        {
            result.push(base as i8);
        }

        result
      }
// </vc-code>


}

fn main() {}