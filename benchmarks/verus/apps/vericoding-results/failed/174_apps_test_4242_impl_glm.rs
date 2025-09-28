// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn common_divisors(a: int, b: int) -> Set<int>
{
  Set::new(|d: int| 1 <= d <= a && a % d == 0 && b % d == 0)
}

spec fn valid_input(a: int, b: int, k: int) -> bool
{
  a > 0 && b > 0 && k >= 1 && common_divisors(a, b).len() >= k
}

spec fn is_kth_largest_common_divisor(a: int, b: int, k: int, result: int) -> bool
{
  valid_input(a, b, k) ==> (
    result > 0 &&
    a % result == 0 && b % result == 0 &&
    common_divisors(a, b).contains(result) &&
    Set::new(|d: int| common_divisors(a, b).contains(d) && d > result).len() == (k - 1)
  )
}
// </vc-preamble>

// <vc-helpers>
fn min(a: int, b: int) -> (result: int)
    ensures result <= a && result <= b && (result == a || result == b)
{
    if a <= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, k: i8) -> (result: i8)
  requires valid_input(a as int, b as int, k as int)
  ensures is_kth_largest_common_divisor(a as int, b as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed set size expression to use .len() */
    let a_int = a as int;
    let b_int = b as int;
    let k_int = k as int;
    let m = min(a_int, b_int);
    let mut divisors_desc = Seq::empty();
    let mut j = m;
    while j >= 1
        invariant
            1 <= j <= m,
            Set::new(|d: int| divisors_desc.contains(d)) == Set::new(|d: int| common_divisors(a_int, b_int).contains(d) && d > j),
            divisors_desc.len() == Set::new(|d: int| common_divisors(a_int, b_int).contains(d) && d > j).len(),
            forall |k: int| 0 <= k < divisors_desc.len()-1 ==> divisors_desc[k] > divisors_desc[k+1]
        decreases j
    {
        if a_int % j == 0 && b_int % j == 0 {
            divisors_desc = divisors_desc.push(j);
        }
        j -= 1;
    }
    let index = k_int - 1;
    let result = divisors_desc[index] as i8;
    result
}
// </vc-code>


}

fn main() {}