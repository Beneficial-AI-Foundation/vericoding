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
/* code modified by LLM (iteration 3): Fix compilation error by replacing `int_to_bit_seq` with `int_to_bit_vec`. */
{
  let dividend_int = Str2Int(dividend@);
  let divisor_int = Str2Int(divisor@);

  let quotient_int = dividend_int / divisor_int;
  let remainder_int = dividend_int % divisor_int;

  let quotient_seq = int_to_bit_vec(quotient_int);
  let remainder_seq = int_to_bit_vec(remainder_int);

  return (quotient_seq,
  remainder_seq);
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
/* code modified by LLM (iteration 3): Fix type error in ModExpPow2 by casting `n - 1` to `nat` and addressing `sy` in recursive call. */
{
  // Base case: If n is 0. The current sy represents 2^0, which is 1.
  // So sy will be ['1']. The result is Str2Int(sx) % Str2Int(sz).
  if n == 0 {
    let sx_int = Str2Int(sx@);
    let sz_int = Str2Int(sz@);
    let result_int = sx_int % sz_int;
    return int_to_bit_vec(result_int);
  }

  // Recursive step: n > 0
  // We need to calculate x' = (sx ^ (2^(n-1))) % sz
  // Then the result is (x' * x') % sz

  // Construct sy for 2^(n-1)
  let sy_n_minus_1_vec = create_sy_for_n_minus_1_char(n);

  // Recursive call to get x'
  let x_prime_vec = ModExpPow2(sx, sy_n_minus_1_vec.as_slice(), (n - 1) as int, sz);
  let x_prime_int = Str2Int(x_prime_vec@);

  // Calculate (x_prime_int * x_prime_int) % sz_int
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
    while current_value > 0_nat
      invariant
        current_value >= 0,
        ValidBitString(result_vec@)
      decreases current_value
    {
      let bit = if current_value % 2 == 1 { '1' } else { '0' };
      result_vec.insert(0, bit);
      current_value = current_value / 2;
    }
    result_vec
  }
}

// Helper to create the sy parameter for the recursive call (2^(n-1))
// For k=1, sy should be '1' (representing 2^0)
// For k=2, sy should be '01' (representing 2^1)
// For k=3, sy should be '001' (representing 2^2)
// For k (where the target exponent is 2^(k-1)), the `sy` bit string should have length `k`.
// It should be '0' repeated `(k-1)` times, followed by '1'.
fn create_sy_for_n_minus_1_char(k: int) -> (s: Vec<char>)
  requires k >= 1 // n-1 cannot be negative
  ensures s.len() == (k as nat),
    ValidBitString(s@),
    Str2Int(s@) == Exp_int(2, (k - 1) as nat)
{
  let mut sy_vec: Vec<char> = Vec::new();
  // For 2^(k-1), the length of the binary representation should be k.
  // This means k-1 leading zeros and a '1' at the end.
  for _i in 0..(k - 1) {
    sy_vec.push('0');
  }
  sy_vec.push('1');
  sy_vec
}
// </vc-code>

fn main() {}
}


