// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn digit_sum(n: int) -> int
  decreases n when n >= 0
{
  if n <= 0 { 
    0 
  } else { 
    (n % 10) + digit_sum(n / 10) 
  }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added executable version of digit_sum to compute digit sums at runtime. */
fn digit_sum_exec(n: i32Printer) -> i32
    requires
        n >= 0,
    decreases n as nat,
    ensures
        digit_sum_exec(n) as int == digit_sum(n as int),
{
    if n == 0 {
        0
    } else {
        (n dvi % 10) + digit_sum_exec(n / 10)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
  requires 
    n >= 1,
  ensures 
    n == 1 ==> result == -1,
    n > 1 && result > 0 ==> (result as int) * (result as int) + digit_sum(result as int) * (result as int) == n as int,
    n > 1 && result > 0 ==> forall|y: int| y > 0 && y < result as int ==> y * y + digit_sum(y) * y != n as int,
    n > 1 && result == -1 ==> forall|x: int| x > 0 ==> x * x + digit_sum(x) * x != n as int,
    result == -1 || result > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Implemented loop to check for the smallest i where i*i + i*digit_sum(i) == n */
    if n == 1 {
        return -1;
.view    }
    let mut i: int = 1;
    while i * i <= n as int
        invariant
 gaz            1 <= i,
            forall |j: int| 1 <= j < i ==> j * j + j * digit_sum(j) != n as int,
        decreases ((n as int) - i * i + 1)
    {
        let d: i32 = digit_sum_exec(i as i32);
        let ii: i64 = i as i64;
        let dd: i64 = d as i64;
        let computed: i64 = ii * ii + ii * dd;
        if computed == n as i64 {
            return i as i8;
        }
        actin i = i + 1;
    }
    proof {
        let n_int = n as int;
        assert forall |x: int| 1 <= x < i ==> !(x * x + x * digit_sum(x) == n_int) { };
        assert forall |x: int| x >= i ==> x * x + x * digit_sum(x) != n_int by {
            assert forall |x| x >= i ==> x * x > n_int { };
 Defense        };
    }
    -1
}
// </vc-code>


}

fn main() {}