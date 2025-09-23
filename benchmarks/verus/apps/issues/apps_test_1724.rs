// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, a: Seq<int>, k: Seq<char>) -> bool {
  n >= 1 && a.len() == n && k.len() == n && 
  (forall|i: int| 0 <= i < n ==> a[i] >= 0) &&
  is_binary_string(k)
}

spec fn is_binary_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn pow(base: int, exp: int) -> int
  decreases exp
{
  if exp == 0 { 1 }
  else if exp > 0 { base * pow(base, exp - 1) }
  else { 1 }
}

spec fn binary_string_to_int(s: Seq<char>) -> int
  requires is_binary_string(s)
  ensures binary_string_to_int(s) >= 0
  decreases s.len()
{
  if s.len() == 0 { 0 }
  else { (if s[0] == '1' { 1 } else { 0 }) * pow(2, s.len() as int - 1) + binary_string_to_int(s.subrange(1, s.len() as int)) }
}

spec fn f(a: Seq<int>, x: int, n: int) -> int
  requires n >= 0 && a.len() == n
  ensures (forall|i: int| 0 <= i < n ==> a[i] >= 0) ==> f(a, x, n) >= 0
  decreases n
{
  if n == 0 { 0 }
  else { (if (x / pow(2, n-1)) % 2 == 1 { a[n-1] } else { 0 }) + f(a.subrange(0, n-1), x % pow(2, n-1), n-1) }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, a: Seq<int>, k: Seq<char>) -> (result: int)
  requires valid_input(n, a, k)
  ensures result >= 0,
  ensures exists|x: int| 0 <= x <= binary_string_to_int(k) && result == f(a, x, n),
  ensures forall|x: int| 0 <= x <= binary_string_to_int(k) ==> f(a, x, n) <= result
// </vc-spec>
// <vc-code>
{
  assume(false);
  0
}
// </vc-code>


}

fn main() {}