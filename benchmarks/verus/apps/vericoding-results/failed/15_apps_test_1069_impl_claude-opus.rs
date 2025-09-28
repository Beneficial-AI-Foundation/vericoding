// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn string_to_nat(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else if s.len() == 1 {
    (s[0] as int - '0' as int) as nat
  } else {
    string_to_nat(s.subrange(0, s.len() - 1)) * 10 + (s[s.len() - 1] as int - '0' as int) as nat
  }
}

spec fn valid_input(n: Seq<char>) -> bool {
  n.len() > 0 && 
  (forall|i: int| 0 <= i < n.len() ==> '0' <= #[trigger] n[i] <= '9') &&
  (n[0] != '0' || n.len() == 1)
}

spec fn valid_output(result: String) -> bool {
  result@ =~= seq!['4', '\n'] || result@ =~= seq!['0', '\n']
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: String) -> (result: String)
  requires valid_input(n@)
  ensures valid_output(result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fix length access using view operator */
    let mut num: u64 = 0;
    let mut i: usize = 0;
    
    while i < n@.len()
        invariant
            0 <= i <= n@.len(),
            valid_input(n@),
            num <= u64::MAX / 10,
    {
        let digit = n@[i as int] as u64 - '0' as u64;
        num = num * 10 + digit;
        i = i + 1;
    }
    
    if num % 4 == 0 {
        "4\n".to_string()
    } else {
        "0\n".to_string()
    }
}
// </vc-code>


}

fn main() {}