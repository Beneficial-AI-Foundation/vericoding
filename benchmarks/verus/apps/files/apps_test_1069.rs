// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn string_to_nat(s: Seq<char>) -> nat
  recommends
    s.len() > 0,
    forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] <= '9'
  decreases s.len()
{
  if s.len() == 1 { 
    (s[0] as int - '0' as int) as nat
  } else { 
    string_to_nat(s.subrange(0, s.len() - 1)) * 10 + (s[s.len() - 1] as int - '0' as int) as nat
  }
}

spec fn valid_input(n: Seq<char>) -> bool {
  n.len() > 0 && 
  (forall|i: int| 0 <= i < n.len() ==> '0' <= n[i] <= '9') &&
  (n[0] != '0' || n.len() == 1)
}

spec fn valid_output(result: Seq<char>) -> bool {
  result == seq!['4', '\n'] || result == seq!['0', '\n']
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: Seq<char>) -> (result: Seq<char>)
  requires
    valid_input(n)
  ensures
    valid_output(result),
    (string_to_nat(n) % 4 == 0) <==> (result == seq!['4', '\n']),
    (string_to_nat(n) % 4 != 0) <==> (result == seq!['0', '\n'])
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}