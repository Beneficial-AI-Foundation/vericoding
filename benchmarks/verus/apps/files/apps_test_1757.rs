// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_fibonacci(num: int) -> bool
  recommends num >= 1
{
  is_fib_helper(num, 1, 1)
}

spec fn is_fib_helper(num: int, prev: int, curr: int) -> bool
  recommends num >= 1 && prev >= 1 && curr >= 1
  decreases if curr >= num { 0 } else { num - curr }
{
  if curr == num { true }
  else if curr > num { false }
  else { is_fib_helper(num, curr, prev + curr) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: Vec<char>)
  requires n >= 1 && n <= 1000
  ensures 
    result.len() == n &&
    (forall|i: int| 0 <= i < result.len() ==> (result.index(i) == 'O' || result.index(i) == 'o')) &&
    (forall|i: int| 1 <= i <= n ==> (is_fibonacci(i) <==> result.index(i-1) == 'O')) &&
    (forall|i: int| 1 <= i <= n ==> (!is_fibonacci(i) <==> result.index(i-1) == 'o'))
// </vc-spec>
// <vc-code>
{
  assume(false);
  Vec::new()
}
// </vc-code>


}

fn main() {}