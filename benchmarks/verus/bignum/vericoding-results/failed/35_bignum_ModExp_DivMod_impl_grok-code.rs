// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, (s.len() - 1) as int)) + (if s[(s.len() - 1) as int] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
  requires 
      valid_bit_string(dividend) && valid_bit_string(divisor) &&
      str2int(divisor) > 0
  ensures 
      valid_bit_string(result.0) && valid_bit_string(result.1) &&
      str2int(result.0) == str2int(dividend) / str2int(divisor) &&
      str2int(result.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 6): Removed 'tracked' from 'let mut' declarations to fix compilation errors, as tracked local variables cannot be mutable in exec context. */
fn seq_to_vec(s: Seq<char>) -> (result: Vec<char>)
{
  let mut v = Vec::new();
  let mut i: usize = 0;
  let len: usize = s.len();
  while i < len
    invariant
      0 <= i <= len,
      valid_bit_string(s),
    decreases len - i
  {
    v.push(s[i as int]);
    i += 1;
  }
  v
}

fn add_binary(a: Seq<char>, b: Seq<char>) -> (result: Seq<char>)
  requires
    valid_bit_string(a),
    valid_bit_string(b),
  ensures
    valid_bit_string(result),
    str2int(result) == str2int(a) + str2int(b),
{
  let len_a: usize = a.len();
  let len_b: usize = b.len();
  let len: usize = if len_a >= len_b { len_a } else { len_b };
  let padding_a: usize = len - len_a;
  let a_pad = Seq::new(padding_a as nat, '0').add(a);
  let padding_b: usize = len - len_b;
  let b_pad = Seq::new(padding_b as nat, '0').add(b);
  let mut result_vec: Vec<char> = Vec::new();
  let mut carry = 0;
  for pos in 0..len
    decreases len - pos
  {
    let index = len - 1 - pos;
    let bit_a = if a_pad[index as int] == '1' { 1 } else { 0 };
    let bit_b = if b_pad[index as int] == '1' { 1 } else { 0 };
    let sum = bit_a + bit_b + carry;
    let next_char = if sum % 2 == 1 { '1' } else { '0' };
    result_vec.push(next_char);
    carry = sum / 2;
  }
  if carry == 1 {
    result_vec.push('1');
  }
  let result_seq = result_vec@;
  let rev_len: usize = result_seq.len();
  let mut reversed = Seq::empty();
  let mut j: usize = 0;
  while j < rev_len
    invariant
      j <= rev_len,
      reversed.len() == j,
      valid_bit_string(result_seq),
    decreases rev_len - j
  {
    let index = rev_len - 1 - j;
    reversed = reversed.add(result_seq[index as int]);
    j += 1;
  }
  reversed
}

fn shift_left(s: Seq<char>, k: usize) -> (result: Seq<char>)
  requires
    valid_bit_string(s),
  ensures
    valid_bit_string(result),
    str2int(result) == str2int(s) * exp_int(2, k as nat),
  decreases k
{
  if k == 0 {
    s
  } else {
    shift_left(s, k - 1).add(seq!['0'])
  }
}

fn multiply_binary(a: Seq<char>, b: Seq<char>) -> (result: Seq<char>)
  requires
    valid_bit_string(a),
    valid_bit_string(b),
  ensures
    valid_bit_string(result),
    str2int(result) == str2int(a) * str2int(b),
  decreases b.len()
{
  let mut acc = seq!['0'];
  let len_b_usize: usize = b.len();
  let mut i: usize = 0;
  while i < len_b_usize
    invariant
      i <= len_b_usize,
      valid_bit_string(acc),
    decreases len_b_usize - i
  {
    if b[i as int] == '1' {
      let sh = shift_left(a, (len_b_usize as int) - 1 - (i as int));
      acc = add_binary(acc, sh);
    }
    i += 1;
  }
  acc
}

fn multiply_mod(a: Seq<char>, b: Seq<char>, m: Seq<char>) -> (result: Seq<char>)
  requires
    valid_bit_string(a),
    valid_bit_string(b),
    valid_bit_string(m),
    str2int(m) > 0,
  ensures
    valid_bit_string(result),
    str2int(result) == (str2int(a) * str2int(b)) % str2int(m),
  decreases m.len()
{
  let prod = multiply_binary(a, b);
  let (quot, rem) = div_mod(prod, m);
  rem
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
      valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
      sy@.len() > 0 && str2int(sz@) > 1
  ensures 
      valid_bit_string(res@) &&
      str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 6): Removed 'tracked' from local declarations to fix potential compilation issues in exec context. */
  let sx_seq = sx@;
  let sy_seq = sy@;
  let sz_seq = sz@;
  let (quot, rem) = div_mod(sx_seq, sz_seq);
  let mut current_base = rem;
  let mut result = seq!['1'];
  let len_sy = sy@.len();
  let ln_sy: int = len_sy as int;
  let mut i: int = 0;
  while i < ln_sy
    invariant
      valid_bit_string(result),
      valid_bit_string(current_base),
      0 <= i <= ln_sy,
    decreases ln_sy - i
  {
    if sy_seq[i] == '1' {
      result = multiply_mod(result, current_base, sz_seq);
    }
    current_base = multiply_mod(current_base, current_base, sz_seq);
    i += 1;
  }
  seq_to_vec(result)
}
// </vc-code>


}

fn main() {}