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
/* helper modified by LLM (iteration 5): Corrected `result` in ensurers for get_common_divisors_desc_seq. */
spec fn get_common_divisors_desc_seq(a: int, b: int) -> Seq<int>
  ensures
    (common_divisors(a, b).len() == 0 ==> result.len() == 0),
    (common_divisors(a, b).len() > 0 ==> {
      &&& result.len() == common_divisors(a, b).len()
      &&& forall |i: int| #![auto]
          0 <= i < result.len() ==> common_divisors(a, b).contains(result[i])
      &&& forall |i: int| #![auto]
          0 <= i < result.len() ==> a % result[i] == 0 && b % result[i] == 0
      &&& forall |i: int| #![auto]
          0 <= i < result.len() - 1 ==> result[i] > result[i+1]
      &&& forall |d: int| #![auto]
          common_divisors(a, b).contains(d) ==> 
            exists |i: int| 0 <= i < result.len() && result[i] == d
    })
{
  let mut divisors: Seq<int> = Seq::empty();
  if a == 0 || b == 0 { return divisors; }

  let max_val = if a > b { a } else { b };
  let mut i = 1;
  while i <= max_val
    invariant
      1 <= i <= max_val + 1,
      forall |d: int| #![auto]
        1 <= d < i && a % d == 0 && b % d == 0 ==> divisors.contains(d),
      forall |d: int| #![auto]
        divisors.contains(d) ==> a % d == 0 && b % d == 0 && d < i
  {
    if a % i == 0 && b % i == 0 {
      divisors = divisors.push_back(i);
    }
    i = i + 1;
  }

  let sorted_divisors = divisors.sort_by(|x, y| y.cmp(x));

  proof {
    assert forall |d: int| #![auto]
      common_divisors(a, b).contains(d) implies (exists |idx: int| 0 <= idx < divisors.len() && divisors[idx] == d)
    by {
      // The existing assertion is not useful here. The key is that `d` must have been added to `divisors` when `i` was equal to `d`.
    }
  }
  sorted_divisors
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, k: i8) -> (result: i8)
  requires valid_input(a as int, b as int, k as int)
  ensures is_kth_largest_common_divisor(a as int, b as int, k as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type errors by casting to relevant types later and addressed scope issues. */
{
  let common_divisors_seq = get_common_divisors_desc_seq(a as int, b as int);

  // k is 1-indexed, so we subtract 1 for 0-indexed sequence access
  let k_val = k as int;

  // This assertion helps Verus understand the relationship between common_divisors_seq and the input validity.
  // This ensures that the sequence access `common_divisors_seq[k_val - 1]` is safe.
  if common_divisors_seq.len() > 0 {
      assert((valid_input(a as int, b as int, k as int) ==> common_divisors_seq.len() >= k_val));
  }

  let result_int = common_divisors_seq[k_val - 1];
  result_int as i8
}
// </vc-code>


}

fn main() {}