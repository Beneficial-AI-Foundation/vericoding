// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, l: Seq<int>) -> bool {
    n >= 1 && k >= 1 && l.len() == n && k <= n * (n + 1) / 2
}

spec fn total_identifiers_after_robot(i: int) -> int 
    recommends i >= 0
{
    i * (i + 1) / 2
}

spec fn correct_result(n: int, k: int, l: Seq<int>, result: int) -> bool
    recommends valid_input(n, k, l)
{
    exists|i: int| #[trigger] total_identifiers_after_robot(i) > 0 &&
      1 <= i <= n && 
      total_identifiers_after_robot(i - 1) < k <= total_identifiers_after_robot(i) &&
      result == l[k - total_identifiers_after_robot(i - 1) - 1]
}
// </vc-preamble>

// <vc-helpers>
fn find_day(k: int, n: int) -> (i: int)
    requires 1 <= k <= n * (n+1) / 2
    ensures 1 <= i <= n && 
            (i-1)*i/2 < k <= i*(i+1)/2
{
    let mut i = 1;
    while (i * (i+1)) / 2 < k
        invariant 1 <= i <= n,
    {
        i = i + 1;
    }
    i
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, l: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, k as int, l@.map(|i: int, x: i8| x as int))
    ensures correct_result(n as int, k as int, l@.map(|i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation error by removing malformed invariant */
    let i = find_day(k as int, n as int);
    let T_prev = (i - 1) * i / 2;
    let index_int = (k as int) - T_prev - 1;
    let result = l@[index_int];
    result
}
// </vc-code>


}

fn main() {}