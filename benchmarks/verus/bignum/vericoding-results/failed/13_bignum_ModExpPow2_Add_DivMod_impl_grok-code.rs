// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res) && str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) && str2int(divisor) > 0
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1) &&
    str2int(res.0) == str2int(dividend) / str2int(divisor) &&
    str2int(res.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
spec fn pad(s: Seq<char>, total_len: nat) -> Seq<char>
  requires
    valid_bit_string(s),
    total_len >= s.len()
  ensures
    valid_bit_string(pad(s, total_len)),
    pad(s, total_len).len() == total_len,
    pad(s, total_len).take(total_len - s.len()) == Seq::new(total_len - s.len() as int, '0'),
    pad(s, total_len).skip(total_len - s.len()) == s,
    str2int(pad(s, total_len)) == str2int(s)
{
  let mut res = Seq::empty();
  let pad_len = total_len - s.len();
  for i in 0..pad_len {
    res.push('0');
  }
  res = res + s;
  res
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires
    valid_bit_string(s1),
    valid_bit_string(s2)
  ensures
    valid_bit_string(res),
    str2int(res) == str2int(s1) + str2int(s2)
{
  let len1 = s1.len();
  let len2 = s2.len();
  let max_len = if len1 > len2 { len1 } else { len2 };
  let p1 = pad(s1, max_len as nat);
  let p2 = pad(s2, max_len as nat);
  let mut temp: Vec<char> = Vec::new();
  let mut carry: char = '0';
  for pos in 0..max_len {
    let idx = max_len - 1 - pos;
    let bit1 = p1[idx];
    let bit2 = p2[idx];
    let (sum_bit, new_carry) = match (bit1, bit2, carry) {
      ('0', '0', '0') => ('0', '0'),
      ('0', '0', '1') => ('1', '0'),
      ('0', '1', '0') => ('1', '0'),
      ('0', '1', '1') => ('0', '1'),
      ('1', '0', '0') => ('1', '0'),
      ('1', '0', '1') => ('0', '1'),
      ('1', '1', '0') => ('0', '1'),
      ('1', '1', '1') => ('1', '1'),
      _ => ('0', '0'),
    };
    temp.push(sum_bit);
    carry = new_carry;
  }
  if carry == '1' { temp.push('1'); }
  let mut result = Vec::new();
  let new_len = temp.len();
  for j in 0..new_len {
    result.push(temp[new_len - 1 - j]);
  }
  result@
}

fn subtract(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires
    valid_bit_string(s1),
    valid_bit_string(s2),
    str2int(s1) >= str2int(s2)
  ensures
    valid_bit_string(res),
    str2int(res) == str2int(s1) - str2int(s2)
{
  let len1 = s1.len();
  let len2 = s2.len();
  let max_len = if len1 > len2 { len1 } else { len2 };
  let p1 = pad(s1, max_len as nat);
  let p2 = pad(s2, max_len as nat);
  let mut temp: Vec<char> = Vec::new();
  let mut borrow: char = '0';
  for pos in 0..max_len {
    let idx = max_len - 1 - pos;
    let bit1 = p1[idx];
    let bit2 = p2[idx];
    let (diff_bit, new_borrow) = match (bit1, bit2, borrow) {
      ('0', '0', '0') => ('0', '0'),
      ('0', '0', '1') => ('1', '1'),
      ('0', '1', '0') => ('1', '1'),
      ('0', '1', '1') => ('0', '0'),
      ('1', '0', '0') => ('1', '0'),
      ('1', '0', '1') => ('0', '0'),
      ('1', '1', '0') => ('0', '0'),
      ('1', '1', '1') => ('1', '1'),
      _ => ('0', '0'),
    };
    temp.push(diff_bit);
    borrow = new_borrow;
  }
  let mut result = Vec::new();
  let new_len = temp.len();
  for j in 0..new_len {
    result.push(temp[new_len - 1 - j]);
  }
  result@
}

fn shift_left(s: Seq<char>, k: nat) -> (res: Seq<char>)
  requires
    valid_bit_string(s)
  ensures
    valid_bit_string(res),
    str2int(res) == str2int(s) * exp_int(2nat, k)
{
  let mut res = s;
  for _i in 0..k {
    res.push('0');
  }
  res
}

fn multiply(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires
    valid_bit_string(s1),
    valid_bit_string(s2)
  ensures
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
{
  let mut res = Seq::empty();
  for i in 0..s2.len() {
    if s2[i] == '1' {
      let pos = (s2.len() - 1 - i) as nat;
      let shifted = shift_left(s1, pos);
      res = add(res, shifted);
    }
  }
  res
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires
    valid_bit_string(dividend),
    valid_bit_string(divisor),
    str2int(divisor) > 0
  ensures
    valid_bit_string(res.0),
    valid_bit_string(res.1),
    str2int(res.0) == str2int(dividend) / str2int(divisor),
    str2int(res.1) == str2int(dividend) % str2int(divisor),
    str2int(res.1) < str2int(divisor),
    str2int(dividend) == str2int(res.0) * str2int(divisor) + str2int(res.1)
{
  let mut rem: Vec<char> = Vec::from(dividend.iter());
  let mut qu: Vec<char> = Vec::new();
  while str2int(rem@) >= str2int(divisor)
    decreases str2int(rem@) - str2int(divisor)
  {
    rem = Vec::from(subtract(rem@, divisor@).iter());
    qu = Vec::from(add(qu@, Seq::new(['1'])).iter());
  }
  (qu@, rem@)
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    (str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0) &&
    sy@.len() == n as int + 1 &&
    str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    if str2int(sy@) == 0 {
      Vec::new(['1'])
    } else {
      let (_, rem) = div_mod(sx@, sz@);
      Vec::from(rem.iter())
    }
  } else {
    let sub_sy = Vec::from(sy@.subrange(1, sy@.len() as int));
    let half_pow = mod_exp_pow2(sx, sub_sy, (n - 1) as u8, sz);
    let half_sq = Vec::from(multiply(half_pow@, half_pow@).iter());
    let (_, modded) = div_mod(half_sq@, sz@);
    Vec::from(modded.iter())
  }
}
// </vc-code>


}

fn main() {}