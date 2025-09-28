// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t) &&
    t.len() > 0 &&
    (t.len() > 1 ==> t[0] != '0') &&
    (valid_bit_string(s) ==> str2int(s) == str2int(t)),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 7): fixed reverse() call by using a local variable */
spec fn max(a: int, b: int) -> int {
  if a >= b { a } else { b }
}

/* helper modified by LLM (iteration 4): fixed type mismatch in recursive call */
spec fn pow2(n: nat) -> nat
  decreases n
{
  if n == 0 { 1 } else { 2 * pow2((n-1) as nat) }
}

/* helper modified by LLM (iteration 7): fixed reverse() call by using a local variable */
fn add_bit_strings(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
  requires
    valid_bit_string(a@) && valid_bit_string(b@),
  ensures
    valid_bit_string(res@) &&
    str2int(res@) == str2int(a@) + str2int(b@),
{
  let mut i = 0;
  let mut carry = 0;
  let mut result: Vec<char> = Vec::new();

  while i < a.len() || i < b.len() || carry > 0
    invariant
      0 <= i <= max(a.len() as int, b.len() as int) + (if carry != 0 { 1int } else { 0int }),
      carry == 0 || carry == 1,
      str2int(a@.subrange((a@.len()-i) as int, a@.len() as int)) + str2int(b@.subrange((b@.len()-i) as int, b@.len() as int)) 
          == (carry as nat) * pow2(i as nat) + str2int(result@.reverse()),
    decreases max(a.len() as int, b.len() as int) + 1 - i
  {
    let digit_a = if i < a.len() { a[a.len()-1-i] } else { '0' };
    let digit_b = if i < b.len() { b[b.len()-1-i] } else { '0' };

    let da = if digit_a == '1' { 1 } else { 0 };
    let db = if digit_b == '1' { 1 } else { 0 };

    let sum = da + db + carry;
    carry = sum / 2;
    let digit = sum % 2;

    result.push(if digit == 1 { '1' } else { '0' });

    i += 1;
  }

  let mut reversed = Vec::new();
  let mut idx = result.len();
  while idx > 0 {
    reversed.push(result[idx-1]);
    idx -= 1;
  }
  reversed
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) * str2int(s2@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): fixed use of moved value by cloning current */
{
  if s2.len() == 0 {
      return vec!['0'];
  }

  let mut res = vec!['0'];
  let mut current = s1;
  let mut j: isize = (s2.len() as isize) - 1;

  while j >= 0
    invariant
      0 <= (j as int) <= s2@.len() - 1,
      valid_bit_string(res@),
      valid_bit_string(current@),
      current@ == s1@ + seq!['0'; (s2@.len() - 1 - (j as int)) as nat],
      str2int(current@) == str2int(s1@) * pow2((s2@.len() - 1 - (j as int)) as nat),
      str2int(res@) == str2int(s1@) * str2int(s2@.subrange((j as int)+1, s2@.len() as int)),
    decreases (j as int)
  {
    if s2[j as usize] == '1' {
      res = add_bit_strings(res, current.clone());
    }
    current.push('0');
    j -= 1;
  }

  res
}
// </vc-code>


}

fn main() {}