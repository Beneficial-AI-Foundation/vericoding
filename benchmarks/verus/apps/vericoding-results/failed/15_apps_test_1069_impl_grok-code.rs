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
/* helper modified by LLM (iteration 5): Converted string_to_nat_exec to spec fn to enable access to Seq elements and fixed type mismatches with int for lengths */
spec fn string_to_nat_exec(s: Seq<char>) -> (res: int)
    requires
        valid_input(s),
    ensures
        (res as nat) === string_to_nat(s),
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        (s[0] as int - '0' as int) as int
    } else {
        (string_to_nat_exec(s.subrange(0, s.len() - 1)) * 10 + (s[s.len() - 1] as int - '0' as int)) as int
    }
}

/* helper modified by LLM (iteration 5): Updated lemma to match the modified spec helper for type consistency */
proof fn lemma_string_to_nat_exec_correct(s: Seq<char>)
    requires
        valid_input(s),
    ensures
        (string_to_nat_exec(s) as nat) === string_to_nat(s),
    decreases s.len()
{
    if s.len() == 0 {
    } else if s.len() == 1 {
    } else {
        lemma_string_to_nat_exec_correct(s.subrange(0, s.len() - 1));
        assert((string_to_nat_exec(s.subrange(0, s.len() - 1)) as nat) === string_to_nat(s.subrange(0, s.len() - 1)));
        assert((string_to_nat_exec(s) as nat) === string_to_nat(s));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: String) -> (result: String)
  requires valid_input(n@)
  ensures valid_output(result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Updated to cast the spec helper's int result to u64 for exec computation */
{
    proof {
        lemma_string_to_nat_exec_correct(n@);
    }
    let num = (string_to_nat_exec(n@) as u64);
    if num % 4 == 0 {
        "0\n".to_string()
    } else {
        "4\n".to_string()
    }
}
// </vc-code>


}

fn main() {}