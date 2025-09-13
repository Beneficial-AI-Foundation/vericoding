// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn mod_value() -> int { 998244353int }

spec fn valid_input(n: int) -> bool
{
  n >= 1
}

#[verifier::external_body]
spec fn pow(base: int, exp: int, modulus: int) -> int
{
  unimplemented!()
}

spec fn block_count_formula(n: int, i: int) -> int
  recommends n >= 1 && 1 <= i <= n
{
  if i == n {
    10int
  } else {
    ((2int * 9int * pow(10int, n - i - 1int, mod_value()) * 10int) + 
     (if i < n - 1int { ((n - 1int - i) * 9int * 9int * pow(10int, n - i - 2int, mod_value()) * 10int) } else { 0int })) % mod_value()
  }
}

spec fn valid_result(result: Seq<int>, n: int) -> bool
  recommends n >= 1
{
  result.len() == n &&
  (forall|k: int| 0 <= k < n ==> 0 <= result[k] < mod_value()) &&
  (n >= 1 ==> result[n-1] == 10int) &&
  (forall|i: int| 0 <= i < n-1 ==> result[i] == block_count_formula(n, i+1))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: Vec<int>)
  requires valid_input(n)
  ensures valid_result(result@, n)
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}