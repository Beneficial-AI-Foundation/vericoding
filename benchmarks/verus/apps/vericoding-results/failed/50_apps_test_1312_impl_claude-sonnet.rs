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
/* helper modified by LLM (iteration 5): Fixed compilation error by removing cast in subrange call */
fn lemma_sum_distribution(result: Seq<int>, n: int, m: int)
    requires
        m > 0,
        result.len() == m,
        (forall|i: int| 0 <= i < result.len() ==> result[i] == n / m || result[i] == n / m + 1),
        count(result, n / m) == m - (n % m),
        count(result, n / m + 1) == n % m,
    ensures sum(result) == n
    decreases result.len()
{
    if result.len() == 0nat {
    } else {
        let first = result[0int];
        let rest = result.subrange(1int, result.len());
        if first == n / m {
            assert(count(rest, n / m) == count(result, n / m) - 1);
            assert(count(rest, n / m + 1) == count(result, n / m + 1));
        } else {
            assert(first == n / m + 1);
            assert(count(rest, n / m) == count(result, n / m));
            assert(count(rest, n / m + 1) == count(result, n / m + 1) - 1);
        }
        lemma_sum_distribution(rest, n, m);
    }
}

fn lemma_count_properties(v: Vec<i8>, val: int, other: int)
    requires val != other
    ensures count(v@.map(|i: int, x: i8| x as int), val) + count(v@.map(|i: int, x: i8| x as int), other) <= v.len()
{
}

fn lemma_vec_properties(v: Vec<i8>, n: int, m: int)
    requires
        m > 0,
        v.len() == m,
        (forall|i: int| 0 <= i < v.len() ==> v[i] as int == n / m || v[i] as int == n / m + 1),
    ensures
        count(v@.map(|i: int, x: i8| x as int), n / m) + count(v@.map(|i: int, x: i8| x as int), n / m + 1) == m
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: Vec<i8>)
  requires valid_input(n as int, m as int)
  ensures optimal_distribution(result@.map(|i: int, x: i8| x as int), n as int, m as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by removing cast in subrange call */
    let mut result = Vec::new();
    let base = (n / m) as i8;
    let remainder = (n % m) as i8;
    
    let mut i = 0i8;
    while i < m
        invariant
            0 <= i <= m,
            result.len() == i,
            (forall|j: int| 0 <= j < result.len() ==> result[j] as int == n as int / m as int || result[j] as int == n as int / m as int + 1),
            count(result@.map(|k: int, x: i8| x as int), n as int / m as int) + count(result@.map(|k: int, x: i8| x as int), n as int / m as int + 1) == i,
    {
        if i < remainder {
            result.push(base + 1);
        } else {
            result.push(base);
        }
        i = i + 1;
    }
    
    proof {
        assert(result.len() == m);
        assert(forall|j: int| 0 <= j < result.len() ==> result[j] as int > 0);
        assert(count(result@.map(|k: int, x: i8| x as int), n as int / m as int) == (m - remainder) as int);
        assert(count(result@.map(|k: int, x: i8| x as int), n as int / m as int + 1) == remainder as int);
        lemma_sum_distribution(result@.map(|k: int, x: i8| x as int), n as int, m as int);
    }
    
    result
}
// </vc-code>


}

fn main() {}