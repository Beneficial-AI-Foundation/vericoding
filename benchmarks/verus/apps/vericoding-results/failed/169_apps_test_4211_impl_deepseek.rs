// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, b: Seq<int>) -> bool {
  n >= 2 && b.len() == n - 1 && forall|i: int| 0 <= i < b.len() ==> b[i] >= 0
}

spec fn sum_mins(b: Seq<int>, len: int) -> int
  decreases len
{
  if len <= 0 {
    0
  } else {
    b[len - 1] + sum_mins(b, len - 1)
  }
}

spec fn correct_result(n: int, b: Seq<int>, result: int) -> bool {
  valid_input(n, b) ==> {
    if n == 2 {
      result == 2 * b[0]
    } else {
      result == b[0] + b[n-2] + sum_mins(b, n-2)
    }
  }
}
// </vc-preamble>

// <vc-helpers>
fn compute_result(n: int, b: Seq<int>) -> (result: int)
    requires
        valid_input(n, b),
    ensures
        correct_result(n, b, result),
    decreases n
{
    if n == 2 {
        2 * b[0]
    } else {
        b[0] + b.index(n - 2) + sum_mins(b, n - 2)
    }
}

spec fn sum_mins_helper(b: Seq<i8>, len: int) -> i8
    decreases len
{
    if len <= 0 {
        0
    } else {
        b.index(len - 1) as i8 + sum_mins_helper(b, len - 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, b: Vec<i8>) -> (result: i8)
  requires valid_input(n as int, b@.map(|i: int, x: i8| x as int))
  ensures correct_result(n as int, b@.map(|i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix type mismatches and indexing */
    let n_int = n as int;
    let b_seq = b@.map(|i: int, x: i8| x as int);
    
    if n == 2 {
        2 * b[0]
    } else {
        let mut sum: i8 = 0;
        let mut i: i8 = 0;
        let limit = (n - 2) as i8;
        
        while i < limit
            invariant
                0 <= i <= limit,
                sum == sum_mins_helper(b@, i as int),
            decreases limit - i
        {
            sum = sum + b.index(i as usize);
            i = i + 1;
        }
        
        b.index(0) + b.index((n - 2) as usize) + sum
    }
}
// </vc-code>


}

fn main() {}