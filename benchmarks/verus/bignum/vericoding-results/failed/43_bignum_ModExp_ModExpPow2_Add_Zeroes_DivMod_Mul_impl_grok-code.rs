// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 {
    0nat
  } else {
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
    sy.len() == n + 1,
    str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  assume(false);
  unreached()
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s)
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (ret: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor),
    str2int(divisor) > 0
  ensures 
    valid_bit_string(ret.0) && valid_bit_string(ret.1),
    str2int(ret.0) == str2int(dividend) / str2int(divisor),
    str2int(ret.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
fn zeros(n: nat) -> (s: Seq<char>)
  ensures
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s)
{
  if n == 0 {
    Seq::empty()
  } else {
    Seq::new(n, |_| '0')
  }
}

fn append_zeros(s: Seq<char>, n: nat) -> Seq<char>
  ensures
    valid_bit_string(s)
  decreases n
{
  if n == 0 {
    s
  } else {
    Seq::append(s, zeros(1))
  }
}

fn less_or_equal(s1: Seq<char>, s2: Seq<char>) -> (res: bool)
{
  if s1.len() < s2.len() {
    true
  } else if s1.len() > s2.len() {
    false
  } else {
    let mut equal_so_far = true;
    let mut less = false;
    let mut i = 0;
    while i < s1.len()
      invariant
        0 <= i <= s1.len(),
        less_or_equal(s1.subrange(0, i), s2.subrange(0, i))
    {
      if equal_so_far {
        if s1[i] == '0' && s2[i] == '1' {
          less = true;
          equal_so_far = false;
        } else if s1[i] == '1' && s2[i] == '0' {
          equal_so_far = false;
        }
      }
      i += 1;
    }
    if less {
      true
    } else {
      equal_so_far
    }
  }
}

fn subtract(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires
    less_or_equal(s2, s1)
  ensures
    valid_bit_string(res),
    str2int(res) == str2int(s1) - str2int(s2)
{
  let len1 = s1.len();
  let len2 = s2.len();
  let max_len = if len1 >= len2 { len1 } else { len2 };
  let mut res = Seq::<char>::empty();
  let mut borrow = 0;
  for i in 0..max_len {
    let idx = max_len as int - 1 - i;
    let b1 = if idx < len1 as int { if s1[idx as nat] == '1' { 1 } else { 0 } } else { 0 };
    let b2 = if idx < len2 as int { if s2[idx as nat] == '1' { 1 } else { 0 } } else { 0 };
    let diff = b1 - b2 - borrow;
    if diff >= 0 {
      res = Seq::push_front(res, if diff % 2 == 1 { '1' } else { '0' });
      borrow = 0;
    } else {
      res = Seq::push_front(res, if (diff + 2) % 2 == 1 { '1' } else { '0' });
      borrow = 1;
    }
  }
  // remove leading zeros
  let mut start = 0;
  for j in 0..res.len() {
    if res[j] == '1' {
      start = j;
      break;
    }
  }
  if start == 0 && res.len() == 0 {
    Seq::empty()
  } else {
    res.subrange(start, res.len())
  }
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  ensures
    valid_bit_string(res),
    str2int(res) == str2int(s1) + str2int(s2)
{
  let len1 = s1.len();
  let len2 = s2.len();
  let max_len = if len1 >= len2 { len1 } else { len2 };
  let mut res = Seq::<char>::empty();
  let mut carry = 0;
  for i in 0..max_len {
    let idx = max_len as int - 1 - i;
    let b1 = if idx < len1 as int { if s1[idx as nat] == '1' { 1 } else { 0 } } else { 0 };
    let b2 = if idx < len2 as int { if s2[idx as nat] == '1' { 1 } else { 0 } } else { 0 };
    let sum = b1 + b2 + carry;
    res = Seq::push_front(res, if sum % 2 == 1 { '1' } else { '0' });
    carry = sum / 2;
  }
  if carry > 0 {
    res = Seq::push_front(res, '1');
  }
  res
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  ensures
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
  decreases s2.len()
{
  if s1.len() == 0 || s2.len() == 0 {
    Seq::empty()
  } else {
    let mut result = zeros(0);
    for i in 0..s2.len() {
      let j = s2.len() - 1 - i;
      if s2[j] == '1' {
        let shifted = append_zeros(s1, i as nat);
        result = add(result, shifted);
      }
    }
    result
  }
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (ret: (Seq<char>, Seq<char>))
  ensures
    valid_bit_string(ret.0),
    valid_bit_string(ret.1),
    str2int(ret.0) == str2int(dividend) / str2int(divisor),
    str2int(ret.1) == str2int(dividend) % str2int(divisor)
  decreases dividend.len()
{
  let mut q = zeros(0);
  let mut r = dividend;
  while less_or_equal(divisor, r) {
    r = subtract(r, divisor);
    q = add(q, Seq::from(['1']));
  }
  (q, r)
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  ensures
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  if n == 0 {
    if str2int(sy) == 0 {
      // return 0 % sz, but since sz >0, 1 % sz =1, but if sy="0", 1 % sz
      let one = Seq::from(['1']);
      div_mod(one, sz).1
    } else {
      // sy="1", sx^1 % sz
      div_mod(sx, sz).1
    }
  } else {
    let sq = mul(sx, sx);
    let sq_mod = div_mod(sq, sz).1;
    let sy_new = zeros(n);
    let sy_new_pad = Seq::push_front(sy_new, '1');
    mod_exp_pow2(sq_mod, sy_new_pad, (n - 1) as nat, sz)
  }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    sy.len() > 0 && str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
  let mut result = zeros(0);
  result = add(result, Seq::from(['1']));
  result = div_mod(result, sz).1;
  let mut base = div_mod(sx, sz).1;
  let mut exponent = sy;
  while exponent.len() > 0 && !all_zero(exponent)
    decreases exponent.len()
  {
    let last = exponent[exponent.len() - 1];
    if last == '1' {
      let temp = mul(result, base);
      result = div_mod(temp, sz).1;
    }
    let base_sq = mul(base, base);
    base = div_mod(base_sq, sz).1;
    if exponent.len() > 1 {
      exponent = exponent.subrange(0, exponent.len() - 1);
    } else {
      exponent = zeros(0);
    }
  }
  result
}
// </vc-code>


}

fn main() {}