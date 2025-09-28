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
/* helper modified by LLM (iteration 3): implementation of addition for bit strings */
fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2),
{
  let mut result = Seq::new();
  let mut carry = 0;
  let mut i = if s1.len() > 0 { s1.len() - 1 } else { -1 };
  let mut j = if s2.len() > 0 { s2.len() - 1 } else { -1 };
  while i >= 0 || j >= 0 || carry > 0
    invariant
      valid_bit_string(result),
      i >= -1 && j >= -1 && carry <= 1 && carry >= 0,
    decreases (if i >= 0 { i as nat } else { 0 }) + (if j >= 0 { j as nat } else { 0 }) + carry,
  {
    let bit1 = if i >= 0 { if s1[i] == '1' { 1 } else { 0 } } else { 0 };
    let bit2 = if j >= 0 { if s2[j] == '1' { 1 } else { 0 } } else { 0 };
    let sum = bit1 + bit2 + carry;
    carry = sum / 2;
    let bit = sum % 2;
    let ch = if bit == 1 { '1' } else { '0' };
    result = result.insert(0, ch);
    if i >= 0 { i = i - 1; }
    if j >= 0 { j = j - 1; }
  }
  if result.len() == 0 {
    result = result.push('0');
  }
  result
}

/* helper modified by LLM (iteration 3): implementation of normalization for bit strings */
fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t) &&
    t.len() > 0 &&
    (t.len() > 1 ==> t[0] != '0') &&
    (valid_bit_string(s) ==> str2int(s) == str2int(t)),
{
  let mut t = s;
  proof {
    if valid_bit_string(s) {
      assert(str2int(s) == str2int(t));
    }
  }
  if t.len() == 0 {
    t = t.push('0');
  }
  while t.len() > 1 && t[0] == '0'
    invariant
      valid_bit_string(t),
      t.len() > 0,
      (valid_bit_string(s) ==> str2int(s) == str2int(t)),
    decreases t.len(),
  {
    t = t.subrange(1, t.len());
  }
  t
}

/* helper modified by LLM (iteration 3): spec function for replicating bit strings */
spec fn replicate(s: Seq<char>, n: int) -> Seq<char>
  requires n >= 0,
  ensures replicate(s, n).len() == s.len() + n,
{
  if n == 0 {
    s
  } else {
    replicate(s, n - 1).push('0')
  }
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
{
  /* code modified by LLM (iteration 3): implementing mul with normalization, partial results, and addition */
  let mut result_vec = Vec::new();
  let s1_normalized = normalize_bit_string(s1@);
  let s2_len = s2@.len();
  let mut partial_results = Vec::new();
  for i in 0..s2_len
    invariant
      valid_bit_string(s1@) && valid_bit_string(s2@) ==> (forall|j| 0 <= j < partial_results.len() ==> valid_bit_string(partial_results[j]@)),
    decreases s2_len - i,
  {
    let bit = if s2@[i] == '1' { 1 } else { 0 };
    let shifted_s1 = if bit == 1 { replicate(s1_normalized, i) } else { Seq::new() };
    partial_results.push(shifted_s1);
  }
  let mut result_seq = Seq::new();
  for p in partial_results
    invariant
      valid_bit_string(result_seq),
  {
    result_seq = add(result_seq, p@);
  }
  for c in result_seq {
    result_vec.push(c);
  }
  proof {
    if valid_bit_string(s1@) && valid_bit_string(s2@) {
      assert(str2int(s1_normalized) == str2int(s1@));
      assert(str2int(result_seq) == str2int(s1@) * str2int(s2@));
    }
  }
  result_vec
}
// </vc-code>


}

fn main() {}