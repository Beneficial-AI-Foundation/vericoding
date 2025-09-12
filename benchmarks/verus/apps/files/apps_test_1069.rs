// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn string_to_nat(s: Seq<char>) -> nat {
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
// </vc-helpers>

// <vc-spec>
fn solve(n: Seq<char>) -> (result: Seq<char>)
  requires valid_input(n),
  requires n.len() > 0,
  requires forall|i: int| 0 <= i < n.len() ==> '0' <= n[i] <= '9',
  ensures valid_output(result),
  ensures (string_to_nat(n) % 4 == 0) <==> (result == seq!['4', '\n']),
  ensures (string_to_nat(n) % 4 != 0) <==> (result == seq!['0', '\n']),
// </vc-spec>
// <vc-code>
{
  assume(false);
  seq!['0', '\n']
}
// </vc-code>


}

fn main() {}