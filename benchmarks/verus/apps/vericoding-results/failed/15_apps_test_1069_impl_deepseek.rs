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
/* helper modified by LLM (iteration 5): fix lemma variable declarations and return type */

proof fn lemma_string_to_nat_nonnegative(s: Seq<char>)
    ensures
        string_to_nat(s) >= 0,
    decreases s.len()
{
    if s.len() == 0 {
    } else if s.len() == 1 {
        assert((s[0] as int - '0' as int) >= 0);
    } else {
        lemma_string_to_nat_nonnegative(s.subrange(0, s.len() - 1));
    }
}

proof fn lemma_string_to_nat_digit_properties(s: Seq<char>)
    requires
        valid_input(s),
    ensures
        forall|i: int| 0 <= i < s.len() ==> (s[i] as int - '0' as int) >= 0,
        forall|i: int| 0 <= i < s.len() ==> (s[i] as int - '0' as int) <= 9,
    decreases s.len()
{
    if s.len() > 0 {
        assert('0' <= s[0] <= '9');
        if s.len() > 1 {
            lemma_string_to_nat_digit_properties(s.subrange(1, s.len()));
        }
    }
}

proof fn lemma_string_to_nat_leading_zero(s: Seq<char>)
    requires
        valid_input(s),
    ensures
        s.len() == 1 || s[0] != '0',
{
}

proof fn lemma_mod4_properties(d: int)
    ensures
        forall|x: int| x % 4 == 0 ==> (x * 10) % 4 == 0,
        forall|x: int| x % 4 == 0 ==> (x * 10 + d) % 4 == d % 4,
        forall|x: int| (x * 10) % 4 == (x % 4 * 10) % 4,
{
}

proof fn lemma_string_to_nat_mod4(s: Seq<char>) -> (r: nat)
    requires
        valid_input(s),
    ensures
        r == string_to_nat(s) % 4,
        r < 4,
    decreases s.len()
{
    lemma_string_to_nat_nonnegative(s);
    lemma_string_to_nat_digit_properties(s);
    
    if s.len() == 0 {
        r = 0;
    } else if s.len() == 1 {
        let digit = (s[0] as int - '0' as int) as nat;
        lemma_mod4_properties(digit);
        r = digit % 4;
    } else {
        let prefix = s.subrange(0, s.len() - 1);
        let last_digit = (s[s.len() - 1] as int - '0' as int) as nat;
        let prefix_mod = lemma_string_to_nat_mod4(prefix);
        lemma_mod4_properties(last_digit);
        r = (prefix_mod * 10 + last_digit) % 4;
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: String) -> (result: String)
  requires valid_input(n@)
  ensures valid_output(result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix result logic and variable usage */
{
    let s = n@;
    let result_mod: nat;
    proof {
        result_mod = lemma_string_to_nat_mod4(s);
    }
    
    let result_str = if result_mod == 0 {
        "4\n".to_string()
    } else {
        "0\n".to_string()
    };
    
    result_str
}
// </vc-code>


}

fn main() {}