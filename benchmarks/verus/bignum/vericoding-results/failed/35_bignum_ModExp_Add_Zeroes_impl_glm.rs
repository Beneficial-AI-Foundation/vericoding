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

spec fn all_zero(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed function signature */
fn add_with_carry(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>, carry: bool)
  requires
    valid_bit_string(s1) && valid_bit_string(s2),
    s1.len() == s2.len(),
  ensures
    res.len() == s1.len(),
    valid_bit_string(res),
    if carry { str2int(res) + 2nat * s1.len() as nat == str2int(s1) + str2int(s2) }
           { str2int(res) == str2int(s1) + str2int(s2) },
{
  let mut res = Seq::empty();
  let mut c = 0;
  let n = s1.len();
  for i in 0..n
    invariant
      0 <= i <= n,
      res.len() == i,
      valid_bit_string(res),
      c == 0 || c == 1,
      str2int(res) + (c as nat) * exp_int(2nat, i as nat) == str2int(s1.subrange(0, i)) + str2int(s2.subrange(0, i)),
    decreases n - i,
  {
    let idx = n - 1 - i;
    let bit1 = if s1[idx] == '1' { 1 } else { 0 };
    let bit2 = if s2[idx] == '1' { 1 } else { 0 };
    let sum = bit1 + bit2 + c;
    let new_bit = if sum % 2 == 1 { '1' } else { '0' };
    res = res.push(new_bit);
    c = sum / 2;
  }
  (res, c != 0)
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy@.len() > 0 && str2int(sz@) > 1,
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed mod_exp implementation */
  let mut result = zeros(1);
  result.push('1');
  
  let y_int = str2int(sy@);
  let z_int = str2int(sz@);
  
  let mut current = sx@;
  let mut exp_remaining = y_int;
  
  while exp_remaining > 0
    invariant
      valid_bit_string(current),
      str2int(result@) == exp_int(str2int(sx@), y_int - exp_remaining) % z_int,
      exp_remaining >= 0,
    decreases exp_remaining,
  {
    if exp_remaining % 2 == 1 {
      let product = multiply(current, result@);
      let mut temp = product;
      
      while str2int(temp) >= z_int
        invariant
          valid_bit_string(temp),
          str2int(temp) >= str2int(product) % z_int,
        decreases str2int(temp),
      {
        temp = subtract(temp, sz@);
      }
      
      result = temp;
    }
    
    let new_current = multiply(current, current);
    let mut temp = new_current;
    
    while str2int(temp) >= z_int
      invariant
        valid_bit_string(temp),
        str2int(temp) >= str2int(new_current) % z_int,
      decreases str2int(temp),
    {
      temp = subtract(temp, sz@);
    }
    
    current = temp;
    exp_remaining = exp_remaining / 2;
  }
  
  result
}
// </vc-code>


}

fn main() {}