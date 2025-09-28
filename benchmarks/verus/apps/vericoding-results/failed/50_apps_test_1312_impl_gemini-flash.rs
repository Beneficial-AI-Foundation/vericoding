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
/* helper modified by LLM (iteration 5): Adding n >= 0 to the requires clause. */
proof fn lemma_division_properties(n: int, m: int)
    requires
        m > 0,
        n >= 0
    ensures
        n == (n / m) * m + (n % m),
        0 <= n % m < m
{}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: Vec<i8>)
  requires valid_input(n as int, m as int)
  ensures optimal_distribution(result@.map(|i: int, x: i8| x as int), n as int, m as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by changing `let mut ghost current_sum: int = 0` to `let mut ghost current_sum = 0i;` to resolve the semicolon expectation. Also fixed the invariants to properly manage `current_sum` for the first loop and correctly assert the composition of `result` in the second loop's invariant. */
{
    let ghost n_i: int = n as int;
    let ghost m_i: int = m as int;

    lemma_division_properties(n_i, m_i);

    let ghost base_value = n_i / m_i;
    let ghost remainder = n_i % m_i;

    let mut result: Vec<i8> = Vec::new();
    let mut ghost current_sum = 0i;
    let mut ghost count_larger_in_result: int = 0;
    let mut i = 0;

    while i < m_i
        invariant
            0 <= i <= m_i,
            result.len() == i as nat,
            count_larger_in_result <= i,
            count_larger_in_result <= remainder,
            // All elements added so far to `result` are either (base_value + 1) or `result` is empty.
            // Specifically, all `count_larger_in_result` elements are (base_value + 1)
            forall|j: int| 0 <= j < count_larger_in_result ==> result.index(j as nat)@ == (base_value + 1) as i8,
            // The parts of the result vector that have been filled. The length of the result vector must be equal to i.
            result@.len() == i,
            // The sum of the elements in the result vector must be equal to `current_sum`.
            current_sum == sum(result@.map(|k: int, x: i8| x as int)),
            current_sum == count_larger_in_result * (base_value + 1),
            // All elements are positive
            forall|j: int| 0 <= j < i ==> result.index(j as nat)@ > 0
        decreases m_i - i
    {
        if count_larger_in_result < remainder {
            result.push((base_value + 1) as i8);
            current_sum = current_sum + (base_value + 1);
            count_larger_in_result = count_larger_in_result + 1;
        } else {
            break;
        }
        i = i + 1;
    }

    let mut ghost count_smaller_in_result: int = 0;
    while i < m_i
        invariant
            0 <= i <= m_i,
            result.len() == i as nat,
            count_larger_in_result == remainder,
            count_smaller_in_result == (i - remainder),
            // Elements before 'remainder' index are (base_value + 1)
            forall|j: int| 0 <= j < remainder ==> result.index(j as nat)@ == (base_value + 1) as i8,
            // Elements from 'remainder' to 'i' are `base_value`
            forall|j: int| remainder <= j < i ==> result.index(j as nat)@ == base_value as i8,
            // Sum of all elements in result
            current_sum == sum(result@.map(|k: int, x: i8| x as int)),
            current_sum == remainder * (base_value + 1) + (i - remainder) * base_value,
            // All elements are positive
            forall|j: int| 0 <= j < i ==> result.index(j as nat)@ > 0
        decreases m_i - i
    {
        result.push(base_value as i8);
        current_sum = current_sum + base_value;
        count_smaller_in_result = count_smaller_in_result + 1;
        i = i + 1;
    }

    result
}
// </vc-code>


}

fn main() {}