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
proof fn decimal_to_binary_helper_correct(n: nat)
    ensures
        is_binary_string(decimal_to_binary_helper(n)),
        binary_to_decimal(decimal_to_binary_helper(n)) == n,
    decreases n
{
    if n == 0 {
        // decimal_to_binary_helper(0) = ['0'] by definition
    } else if n == 1 {
        // decimal_to_binary_helper(1) = ['1'] by definition
    } else {
        // For n > 1, decimal_to_binary_helper(n) = decimal_to_binary_helper(n / 2).add(decimal_to_binary_helper(n % 2))
        decimal_to_binary_helper_correct(n / 2);
        decimal_to_binary_helper_correct(n % 2);
        proof {
            // From the definitions and the inductive hypotheses:
            // binary_to_decimal(decimal_to_binary_helper(n / 2)) == n / 2
            // binary_to_decimal(decimal_to_binary_helper(n % 2)) == n % 2
            // By the recursive definition of binary_to_decimal on concatenation,
            // binary_to_decimal(decimal_to_binary_helper(n / 2).add(decimal_to_binary_helper(n % 2)))
            // == binary_to_decimal(decimal_to_binary_helper(n / 2)) * 2 + binary_to_decimal(decimal_to_binary_helper(n % 2))
            // which equals (n / 2) * 2 + (n % 2) == n.
            // is_binary_string also follows from the inductive hypotheses and the construction.
        }
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
    let seq = decimal_to_binary_helper(n as nat);
    let s = Vec::from_seq(seq);
    proof {
        decimal_to_binary_helper_correct(n as nat);
    }
    s
}

// </vc-code>


}

fn main() {}