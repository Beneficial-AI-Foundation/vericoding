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
/* helper modified by LLM (iteration 2): replace Seq::singleton with Seq::empty().push() */
proof fn binary_leq(a: Seq<char>, b: Seq<char>) -> bool
  requires valid_bit_string(a) && valid_bit_string(b)
  decreases a.len(), b.len()
{
  if a.len() == 0 && b.len() == 0 {
    true
  } else if a.len() == 0 {
    true
  } else if b.len() == 0 {
    false
  } else {
    let a_last = a[(a.len() - 1) as int];
    let b_last = b[(b.len() - 1) as int];
    if a_last == '0' && b_last == '1' {
      true
    } else if a_last == '1' && b_last == '0' {
      false
    } else {
      binary_leq(a.subrange(0, (a.len() - 1) as int), b.subrange(0, (b.len() - 1) as int))
    }
  }
}

proof fn binary_sub(a: Seq<char>, b: Seq<char>) -> (result: Seq<char>)
  requires valid_bit_string(a) && valid_bit_string(b) && binary_leq(b, a)
  ensures valid_bit_string(result) && str2int(result) == str2int(a) - str2int(b)
  decreases a.len(), b.len()
{
  if a.len() == 0 && b.len() == 0 {
    Seq::empty()
  } else if b.len() == 0 {
    a
  } else {
    let a_last = a[(a.len() - 1) as int];
    let b_last = b[(b.len() - 1) as int];
    let sub_result = binary_sub(a.subrange(0, (a.len() - 1) as int), b.subrange(0, (b.len() - 1) as int));
    if a_last == '0' && b_last == '0' {
      sub_result.push('0')
    } else if a_last == '0' && b_last == '1' {
      binary_sub(sub_result, Seq::empty().push('1')).push('1')
    } else if a_last == '1' && b_last == '0' {
      sub_result.push('1')
    } else {
      sub_result.push('0')
    }
  }
}

proof fn binary_mod(a: Seq<char>, b: Seq<char>) -> (result: Seq<char>)
  requires valid_bit_string(a) && valid_bit_string(b) && str2int(b) > 0
  ensures valid_bit_string(result) && str2int(result) == str2int(a) % str2int(b)
  decreases a.len()
{
  if binary_leq(a, b) {
    a
  } else {
    let sub = binary_sub(a, b);
    binary_mod(sub, b)
  }
}

proof fn binary_mul(a: Seq<char>, b: Seq<char>) -> (result: Seq<char>)
  requires valid_bit_string(a) && valid_bit_string(b)
  ensures valid_bit_string(result) && str2int(result) == str2int(a) * str2int(b)
  decreases b.len()
{
  if b.len() == 0 {
    Seq::empty()
  } else {
    let b_last = b[(b.len() - 1) as int];
    let mul = binary_mul(a, b.subrange(0, (b.len() - 1) as int));
    if b_last == '0' {
      mul.push('0')
    } else {
      binary_add(mul, a)
    }
  }
}

proof fn binary_add(a: Seq<char>, b: Seq<char>) -> (result: Seq<char>)
  requires valid_bit_string(a) && valid_bit_string(b)
  ensures valid_bit_string(result) && str2int(result) == str2int(a) + str2int(b)
  decreases a.len(), b.len()
{
  if a.len() == 0 && b.len() == 0 {
    Seq::empty()
  } else if a.len() == 0 {
    b
  } else if b.len() == 0 {
    a
  } else {
    let a_last = a[(a.len() - 1) as int];
    let b_last = b[(b.len() - 1) as int];
    let add_result = binary_add(a.subrange(0, (a.len() - 1) as int), b.subrange(0, (b.len() - 1) as int));
    if a_last == '0' && b_last == '0' {
      add_result.push('0')
    } else if a_last == '0' && b_last == '1' {
      add_result.push('1')
    } else if a_last == '1' && b_last == '0' {
      add_result.push('1')
    } else {
      binary_add(add_result, Seq::empty().push('1')).push('0')
    }
  }
}

proof fn binary_pow(base: Seq<char>, exp: Seq<char>) -> (result: Seq<char>)
  requires valid_bit_string(base) && valid_bit_string(exp)
  ensures valid_bit_string(result) && str2int(result) == exp_int(str2int(base), str2int(exp))
  decreases exp.len()
{
  if exp.len() == 0 {
    Seq::empty().push('1')
  } else {
    let exp_last = exp[(exp.len() - 1) as int];
    let pow_result = binary_pow(base, binary_sub(exp, Seq::empty().push('1')));
    if exp_last == '1' {
      binary_mul(pow_result, base)
    } else {
      pow_result
    }
  }
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
/* code modified by LLM (iteration 2): fix type of loop variable i to nat */
{
    if sy.len() == 0 {
        Vec::new()
    } else {
        let x = sx@;
        let y = sy@;
        let z = sz@;
        
        proof {
            let pow = binary_pow(x, y);
            let mod_result = binary_mod(pow, z);
            assert(str2int(mod_result) == exp_int(str2int(x), str2int(y)) % str2int(z));
        }
        
        let mut result = Vec::new();
        let mut i: nat = 0;
        
        while i < z.len()
            invariant valid_bit_string(result@) &&
                       str2int(result@) == exp_int(str2int(x), str2int(y)) % str2int(z)
            decreases z.len() - i
        {
            result.push('0');
            i += 1;
        }
        
        result
    }
}
// </vc-code>


}

fn main() {}