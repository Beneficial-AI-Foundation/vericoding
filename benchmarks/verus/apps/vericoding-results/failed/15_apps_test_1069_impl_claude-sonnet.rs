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
/* helper modified by LLM (iteration 5): using vstd::arithmetic::power2 module for power of 2 check */
use vstd::arithmetic::power2::*;

spec fn is_power_of_two(n: nat) -> bool {
    exists|k: nat| n == pow2(k)
}

/* helper modified by LLM (iteration 5): removed incorrect lemma keyword usage */
fn lemma_power_of_two_classification(n: nat)
    requires n > 0
    ensures is_power_of_two(n) || !is_power_of_two(n)
{
}

/* helper modified by LLM (iteration 5): fixed lemma declaration syntax */
proof fn lemma_string_to_nat_correctness(s: Seq<char>)
    requires valid_input(s)
    ensures string_to_nat(s) > 0
    decreases s.len()
{
    if s.len() == 1 {
        assert(s[0] >= '0' && s[0] <= '9');
    } else {
        lemma_string_to_nat_correctness(s.subrange(0, s.len() - 1));
    }
}

exec fn char_to_digit(c: char) -> (result: u8)
    requires '0' <= c <= '9'
    ensures result == (c as u8 - '0' as u8)
{
    (c as u8) - ('0' as u8)
}

exec fn string_to_nat_exec(s: &str) -> (result: u64)
    requires valid_input(s@)
    ensures result as nat == string_to_nat(s@)
{
    let mut result: u64 = 0;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result as nat == string_to_nat(s@.subrange(0, i as int))
    {
        let digit = char_to_digit(s.chars().nth(i).unwrap());
        result = result * 10 + digit as u64;
        i += 1;
    }
    result
}

exec fn is_power_of_two_exec(n: u64) -> (result: bool)
    ensures result == is_power_of_two(n as nat)
{
    if n == 0 {
        false
    } else {
        (n & (n - 1)) == 0
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: String) -> (result: String)
  requires valid_input(n@)
  ensures valid_output(result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using exec functions instead of spec functions */
    let num_value = string_to_nat_exec(&n);
    
    proof {
        lemma_string_to_nat_correctness(n@);
        lemma_power_of_two_classification(num_value as nat);
    }
    
    if is_power_of_two_exec(num_value) {
        "4\n".to_string()
    } else {
        "0\n".to_string()
    }
}
// </vc-code>


}

fn main() {}