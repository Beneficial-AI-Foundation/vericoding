use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
  let dividend_int = Str2Int(dividend@);
  let divisor_int = Str2Int(divisor@);

  let quotient_int = dividend_int / divisor_int;
  let remainder_int = dividend_int % divisor_int;

  fn int_to_bit_seq(value: nat) -> (s: Seq<char>)
    ensures ValidBitString(s),
      Str2Int(s) == value
    decreases value
  {
    if value == 0 {
      return Seq::singleton('0');
    } else {
      let mut current_value = value;
      let mut result_seq = Seq::<char>::new();
      while current_value > 0
        invariant
          current_value >= 0,
          ValidBitString(result_seq),
          (Str2Int(result_seq) + Exp_int(2, result_seq.len() as nat) * current_value) == value,
        decreases current_value
      {
        let bit = (current_value % 2 == 1) ? '1' : '0';
        result_seq = Seq::singleton(bit).add(result_seq);
        current_value = current_value / 2;
      }
      result_seq
    }
  }

  let quotient_seq = int_to_bit_seq(quotient_int);
  let remainder_seq = int_to_bit_seq(remainder_int);

  return (quotient_seq.to_vec(), remainder_seq.to_vec());
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
  // Base case: If n is 0, sy is '01' (2^0 = 1), so we return sx % sz
  if n == 0 {
    let sx_int = Str2Int(sx@);
    let sz_int = Str2Int(sz@);
    let result_int = sx_int % sz_int;
    return int_to_bit_vec(result_int);
  }

  // Recursive step: n > 0
  // We need to calculate Exp_int(Str2Int(sx@), Exp_int(2, n as nat)) % Str2Int(sz@)
  // This is equivalent to (X^(2^(n-1)))^2 % M, where X = Str2Int(sx@), M = Str2Int(sz@)

  // Calculate x_prime = Exp_int(Str2Int(sx@), Exp_int(2, (n-1) as nat)) % Str2Int(sz@)
  let sy_n_minus_1 = create_sy_for_n_minus_1(n);
  let x_prime_vec = ModExpPow2(sx, sy_n_minus_1.as_slice(), (n - 1) as int, sz);
  let x_prime_int = Str2Int(x_prime_vec@);

  // Then square x_prime_int and take modulo sz_int
  let sz_int = Str2Int(sz@);
  let final_result_int = (x_prime_int * x_prime_int) % sz_int;

  return int_to_bit_vec(final_result_int);
}

// Helper to convert nat to Vec<char> which represents its binary string
fn int_to_bit_vec(value: nat) -> (s: Vec<char>)
  ensures ValidBitString(s@),
    Str2Int(s@) == value
  decreases value
{
  if value == 0 {
    return vec!['0'];
  } else {
    let mut current_value = value;
    let mut result_vec = Vec::<char>::new();
    while current_value > 0
      invariant
        current_value >= 0,
        ValidBitString(result_vec@),
        (Str2Int(result_vec@) + Exp_int(2, result_vec@.len() as nat) * current_value) == value,
      decreases current_value
    {
      let bit = (current_value % 2 == 1) ? '1' : '0';
      result_vec.insert(0, bit);
      current_value = current_value / 2;
    }
    result_vec
  }
}

// Helper to create the sy parameter for the recursive call (2^(n-1))
// For n=0, sy should be '01' (2^0)
// For n=1, sy should be '01' (representing 1 * 2^0)
// For n=2, sy should be '001' (representing 1 * 2^0)
// For n=k, sy should be '0...01' (k zeros and a 1, length k+1)
fn create_sy_for_n_minus_1(k: int) -> (s: Vec<char>)
  requires k > 0
  ensures s.len() == (k as nat),
    ValidBitString(s@),
    Str2Int(s@) == Exp_int(2, (k - 1) as nat)
{
  let mut sy_vec: Vec<char> = Vec::new();
  sy_vec.push('1');
  for _i in 0..(k - 1) {
    sy_vec.insert(0, '0');
  }
  sy_vec
}
// </vc-code>

fn main() {}
}


