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
/* helper modified by LLM (iteration 5): [no changes needed, helper is correct] */
spec fn seq_contains_char(s: Seq<char>, c: char) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == c
}
// </vc-helpers>

// <vc-spec>
fn solve(n: String) -> (result: String)
  requires valid_input(n@)
  ensures valid_output(result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [fixed type mismatch in loop condition by using n.len()] */
    let n_len = n.len();
    let mut i: usize = 0;
    while i < n_len
        invariant
            i as nat <= n@.len(),
            !seq_contains_char(n@.subrange(0, i as int), '4'),
        decreases n@.len() - i as nat
    {
        if n.as_bytes()[i] as char == '4' {
            return "4\n".to_string();
        }
        i = i + 1;
    }
    "0\n".to_string()
}
// </vc-code>


}

fn main() {}