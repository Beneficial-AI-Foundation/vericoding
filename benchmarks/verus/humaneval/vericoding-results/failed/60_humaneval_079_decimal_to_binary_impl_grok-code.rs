// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_binary_string(s: Seq<char>) -> bool {
  s.len() > 0 && (s.len() > 1 ==> s[0] != '0') &&
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn decimal_to_binary_helper(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    seq!['0']
  } else if n == 1 {
    seq!['1']
  } else {
    decimal_to_binary_helper(n / 2).add(decimal_to_binary_helper(n % 2))
  }
}

spec fn binary_to_decimal(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() <= 0 {
    0
  } else if s.len() == 1 {
    if s[0] == '0' { 0 } else { 1 }
  } else {
    binary_to_decimal(s.take((s.len() - 1) as int)) * 2 + 
    binary_to_decimal(s.skip((s.len() - 1) as int))
  }
}
// </vc-preamble>

// <vc-helpers>
fn decimal_to_binary_exec(n: u8) -> Vec<char>
    decreases n
    ensures
        is_binary_string(result@),
        binary_to_decimal(result@) == n as nat,
{
    if n == 0 {
        vec!['0']
    } else if n == 1 {
        vec!['1']
    } else {
        let mut high = decimal_to_binary_exec(n / 2);
        let low = if n % 2 == 0 { '0' } else { '1' };
        high.push(low);
        high
    }
}
// </vc-helpers>

// <vc-spec>
fn decimal_to_binary(n: u8) -> (s: Vec<char>)
  ensures
    is_binary_string(s@),
    binary_to_decimal(s@) == n as nat,
// </vc-spec>
// <vc-code>
{
    let s = decimal_to_binary_exec(n);
    s
}
// </vc-code>


}

fn main() {}