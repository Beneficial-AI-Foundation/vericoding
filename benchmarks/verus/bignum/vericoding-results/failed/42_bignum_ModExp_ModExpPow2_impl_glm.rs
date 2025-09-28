// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
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
// </vc-preamble>

// <vc-helpers>
proof fn binary_add(a: Seq<char>, b: Seq<char>) -> (sum: Seq<char>)
  requires
    valid_bit_string(a),
    valid_bit_string(b),
    a.len() == b.len()
  ensures
    valid_bit_string(sum),
    sum.len() == a.len() + 1,
    str2int(sum) == str2int(a) + str2int(b)
  decreases a.len()
{
  if a.len() == 0 {
    seq!['0']
  } else {
    let a_tail = a.subrange(0, a.len() - 1);
    let b_tail = b.subrange(0, b.len() - 1);
    let tail_sum = binary_add(a_tail, b_tail);
    let a_bit = if a[a.len() - 1] == '1' { 1nat } else { 0nat };
    let b_bit = if b[b.len() - 1] == '1' { 1nat } else { 0nat };
    let bit_sum = a_bit + b_bit;
    let tail_val = str2int(tail_sum);
    let total = tail_val + bit_sum;
    let new_bit = if total % 2 == 1 { '1' } else { '0' };
    let carry = if total >= 2 { 1 } else { 0 };
    let mut result = tail_sum.push(new_bit);
    if carry == 1 && result.len() == a.len() {
      result = result.push('1');
    } else if carry == 1 {
      let mut new_result = seq!['1'];
      let mut i = 0;
      while i < result.len()
        invariant 0 <= i <= result.len()
        decreases result.len() - i
      {
        new_result = new_result.push(result[i]);
        i = i + 1;
      }
      result = new_result;
    }
    result
  }
}

spec fn binary_mul(a: Seq<char>, b: Seq<char>) -> (prod: Seq<char>)
  decreases a.len()
{
  if a.len() == 0 {
    seq!['0']
  } else {
    let a_tail = a.subrange(0, a.len() - 1);
    let tail_prod = binary_mul(a_tail, b);
    let a_bit = if a[a.len() - 1] == '1' { 1nat } else { 0nat };
    let shift_val = str2int(tail_prod) * 2;
    let add_val = a_bit * str2int(b);
    let total = shift_val + add_val;
    int2bin(total)
  }
}

spec fn int2bin(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    seq!['0']
  } else if n == 1 {
    seq!['1']
  } else {
    let tail = int2bin(n / 2);
    let bit = if n % 2 == 1 { '1' } else { '0' };
    tail.push(bit)
  }
}

spec fn binary_mod(a: Seq<char>, b: Seq<char>) -> (rem: Seq<char>)
  requires str2int(b) > 0
  decreases str2int(a)
{
  if str2int(a) < str2int(b) {
    a
  } else {
    let diff = str2int(a) - str2int(b);
    binary_mod(int2bin(diff), b)
  }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    let n = sy.len() - 1;
    let sx_seq = sx@;
    let sy_seq = sy@;
    let sz_seq = sz@;
    
    let result = mod_exp_pow2(sx_seq, sy_seq, n, sz_seq);
    
    let mut res_vec: Vec<char> = Vec::new();
    let mut i = 0;
    while i < result.len()
        invariant 0 <= i <= result.len()
        decreases result.len() - i
    {
        res_vec.push(result[i]);
        i = i + 1;
    }
    
    res_vec
}
// </vc-code>


}

fn main() {}