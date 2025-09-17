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
  fn compare(a: Seq<char>, b: Seq<char>) -> int
  {
    if a.len() < b.len() as int { -1 }
    else if a.len() > b.len() as int { 1 }
    else {
      for i in 0..a.len() {
        if a[i] < b[i] { return -1; }
        else if a[i] > b[i] { return 1; }
      }
      return 0;
    }
  }

  fn subtract(a: Seq<char>, b: Seq<char>) -> Vec<char>
    requires compare(a, b) >= 0
  {
    let mut result: Vec<char> = Vec::new();
    let mut borrow = 0;
    for i in 0..a.len() {
      let mut bit1 = if a[i] == '1' { 1 } else { 0 };
      bit1 -= borrow;
      bit1 -= if i < b.len() && b[i] == '1' { 1 } else { 0 };
      if bit1 < 0 {
        bit1 += 2;
        borrow = 1;
      } else {
        borrow = 0;
      }
      result.push(if bit1 == 1 { '1' } else { '0' });
    }
    result
  }

  let dividend_seq = dividend@;
  let divisor_seq = divisor@;
  let mut quotient: Vec<char> = Vec::new();
  let mut remainder: Vec<char> = Vec::new();
  for k in 0..(dividend_seq.len() as int) {
    remainder.push(dividend_seq[k]);
    proof {
      reveal_str2int();
      // proof that compare and subtract maintain invariants
    }
    if compare(remainder@, divisor_seq) >= 0 {
      quotient.push('1');
      remainder = subtract(remainder@, divisor_seq);
    } else {
      quotient.push('0');
    }
  }
  (quotient, remainder)
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  fn add_bits(a: Seq<char>, b: Seq<char>) -> Vec<char>
  {
    let max_len = if a.len() > b.len() { a.len() } else { b.len() } as usize;
    let mut result: Vec<char> = Vec::with_capacity(max_len + 1);
    let mut carry = 0;
    for i in 0..max_len {
      let idx = i as int;
      let bit1 = if idx < a.len() && a[idx] == '1' { 1 } else { 0 };
      let bit2 = if idx < b.len() && b[idx] == '1' { 1 } else { 0 };
      let sum = bit1 + bit2 + carry;
      carry = sum / 2;
      let bit = if sum % 2 == 1 { '1' } else { '0' };
      result.push(bit);
    }
    if carry == 1 {
      result.push('1');
    }
    result
  }

  let s1_seq = s1@;
  let s2_seq = s2@;
  let mut result: Vec<char> = vec!['0'];
  let mut shift = 0;
  while shift < s1_seq.len() {
    if s1_seq[shift as int] == '1' {
      let mut shifted: Vec<char> = vec!['0'; shift];
      shifted.extend(s2_seq.into_iter().map(|&c| c));
      result = add_bits(result@, shifted@);
    }
    shift += 1;
  }
  result
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
  fn nat_to_vec(n: nat) -> Vec<char>
  {
    if n == 0 {
      vec!['0']
    } else {
      let mut result: Vec<char> = Vec::new();
      let mut m = n;
      while m > 0 {
        result.push(if m % 2 == 1 { '1' } else { '0' });
        m /= 2;
      }
      result.reverse();
      result
    }
  }

  if n == 0 {
    if Str2Int(sy@) == 0 {
      nat_to_vec(1 % Str2Int(sz@))
    } else {
      nat_to_vec(Str2Int(sx@) % Str2Int(sz@))
    }
  } else {
    let half = ModExpPow2(sx, sy, n - 1, sz);
    let product = Mul(&half, &half);
    let (_, r) = DivMod(&product, sz);
    r
  }
}
// </vc-code>

fn main() {}
}
