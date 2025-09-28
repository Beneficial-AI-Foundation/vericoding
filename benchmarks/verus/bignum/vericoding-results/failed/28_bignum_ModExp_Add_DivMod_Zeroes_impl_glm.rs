// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2_int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    if valid_bit_string(s) {
      2 * str2_int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    } else {
      0nat
    }
  }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2_int(res) == str2_int(s1) + str2_int(s2),
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (quotient_remainder: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2_int(divisor) > 0,
  ensures 
    valid_bit_string(quotient_remainder.0) && valid_bit_string(quotient_remainder.1) &&
    str2_int(quotient_remainder.0) == str2_int(dividend) / str2_int(divisor) &&
    str2_int(quotient_remainder.1) == str2_int(dividend) % str2_int(divisor),
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n &&
    valid_bit_string(s) &&
    str2_int(s) == 0 &&
    all_zero(s),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
fn is_zero(s: Seq<char>) -> bool
{
    let mut i = 0;
    while i < s.len()
        invariant 0 <= i <= s.len()
    {
        if s[i] != '0' {
            return false;
        }
        i += 1;
    }
    true
}

fn last_bit(s: Seq<char>) -> (Seq<char>, char)
    requires valid_bit_string(s) && s.len() > 0,
    ensures valid_bit_string(tail) && (bit == '0' || bit == '1'),
{
    let mut tail = Seq::new();
    let mut i = 0;
    while i < s.len() - 1
        invariant 0 <= i <= s.len() - 1
    {
        tail.push(s[i]);
        i += 1;
    }
    (tail, s[s.len() - 1])
}

fn mod_add(a: Seq<char>, b: Seq<char>, modulus: Seq<char>) -> (res: Seq<char>)
    requires valid_bit_string(a) && valid_bit_string(b) && valid_bit_string(modulus) && str2_int(modulus) > 1,
    ensures valid_bit_string(res) && str2_int(res) == (str2_int(a) + str2_int(b)) % str2_int(modulus),
{
    let mut sum = Seq::new();
    let mut carry = 0;
    let mut i = 0;
    while i < a.len() || i < b.len() || carry != 0
        invariant 0 <= i <= a.len() + 1 && 0 <= i <= b.len() + 1,
        invariant carry == 0 || carry == 1,
    {
        let a_bit = if i < a.len() { if a[a.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let b_bit = if i < b.len() { if b[b.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let total = a_bit + b_bit + carry;
        let bit = total % 2;
        carry = total / 2;
        sum.insert(0, if bit == 1 { '1' } else { '0' });
        i += 1;
    }
    let mut mod_result = Seq::new();
    let mut remainder = 0;
    let mut j = 0;
    while j < sum.len()
        invariant 0 <= j <= sum.len(),
    {
        let current = if remainder == 0 {
            if j < sum.len() && sum[j] == '1' { 1 } else { 0 }
        } else {
            if j < sum.len() && sum[j] == '1' { 2 } else { 1 }
        };
        let mod_bit = current % 2;
        remainder = current / 2;
        mod_result.push(if mod_bit == 1 { '1' } else { '0' });
        j += 1;
    }
    mod_result
}

fn mod_multiply(a: Seq<char>, b: Seq<char>, modulus: Seq<char>) -> (res: Seq<char>)
    requires valid_bit_string(a) && valid_bit_string(b) && valid_bit_string(modulus) && str2_int(modulus) > 1,
    ensures valid_bit_string(res) && str2_int(res) == (str2_int(a) * str2_int(b)) % str2_int(modulus),
{
    let mut product = Seq::new();
    product.push('0');
    let mut i = 0;
    while i < b.len()
        invariant 0 <= i <= b.len(),
        invariant valid_bit_string(product),
    {
        if b[b.len() - 1 - i] == '1' {
            let mut temp = Seq::new();
            let mut j = 0;
            while j < a.len()
                invariant 0 <= j <= a.len(),
            {
                temp.push(a[j]);
                j += 1;
            }
            let mut k = 0;
            while k < i
                invariant 0 <= k <= i,
            {
                temp.push('0');
                k += 1;
            }
            product = mod_add(product, temp, modulus);
        }
        i += 1;
    }
    product
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz) &&
    sy.len() > 0 && str2_int(sz) > 1,
  ensures 
    valid_bit_string(res) &&
    str2_int(res) == exp_int(str2_int(sx), str2_int(sy)) % str2_int(sz),
  decreases sy.len(),
// </vc-spec>
// <vc-code>
{
    if is_zero(sy) {
        let mut one = Seq::new();
        one.push('1');
        one
    } else {
        let (sy_tail, bit) = last_bit(sy);
        let half_exp = mod_exp(sx, sy_tail, sz);
        let square = mod_multiply(half_exp, half_exp, sz);
        if bit == '1' {
            mod_multiply(square, sx, sz)
        } else {
            square
        }
    }
}
// </vc-code>


}

fn main() {}