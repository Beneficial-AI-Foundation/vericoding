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
proof fn lemma_sum_mins_distribute(b: Seq<int>, len: int)
    requires len >= 0, len <= b.len()
    ensures sum_mins(b, len) == (if len <= 0 { 0 } else { b[len - 1] + sum_mins(b, len - 1) })
{
}

proof fn lemma_sum_mins_computation(b: Seq<int>, n: int)
    requires n >= 2, b.len() == n - 1
    ensures sum_mins(b, n - 2) == if n == 2 { 0 } else { b[n - 3] + sum_mins(b, n - 3) }
{
    if n > 2 {
        lemma_sum_mins_distribute(b, n - 2);
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
    /* code modified by LLM (iteration 4): added decreases clause to while loop */
    if n == 2 {
        let result = 2 * b[0];
        result
    } else {
        proof {
            let n_int = n as int;
            let b_int = b@.map(|i: int, x: i8| x as int);
            lemma_sum_mins_computation(b_int, n_int);
        }
        
        let mut sum = 0i8;
        let mut i = 0usize;
        
        while i < (n - 2) as usize
            invariant
                i <= (n - 2) as usize,
                sum as int == sum_mins(b@.map(|i: int, x: i8| x as int), i as int),
            decreases (n - 2) as usize - i
        {
            sum = sum + b[i];
            i = i + 1;
        }
        
        let result = b[0] + b[(n - 2) as usize] + sum;
        result
    }
}
// </vc-code>


}

fn main() {}