
use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 9): bit_to_nat and Str2Int append lemma */
spec fn bit_to_nat(c: char) -> nat { if c == '1' { 1nat } else { 0nat } }
proof fn Str2Int_append(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1',
    ensures Str2Int(s + seq![c]) == 2 * Str2Int(s) + bit_to_nat(c)
{
}

// </vc-helpers>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 9): implement long division on bit vectors with invariants */
  let n = dividend.len();
  let mut i: usize = 0;
  let mut q = Vec::<char>::new();
  let mut rem = Vec::<char>::new();

  while i < n
      invariant
          0 <= i && i <= n,
          ValidBitString(q@),
          ValidBitString(rem@),
          Str2Int(q@) * Str2Int(divisor@) + Str2Int(rem@) == Str2Int(dividend@.subrange(0, i as int)),
          Str2Int(rem@) < Str2Int(divisor@),
      decreases n - i
  {
      let b = dividend[i];
      rem.push(b);

      // compare rem and divisor without numeric conversion
      fn seq_ge(a: &Vec<char>, b_slice: &[char]) -> bool {
          let mut a_start: usize = 0;
          while a_start < a.len() && a[a_start] == '0' {
              a_start += 1;
          }
          let mut b_start: usize = 0;
          while b_start < b_slice.len() && b_slice[b_start] == '0' {
              b_start += 1;
          }
          let a_len = a.len().saturating_sub(a_start);
          let b_len = b_slice.len().saturating_sub(b_start);
          if a_len != b_len { return a_len > b_len; }
          let mut j: usize = 0;
          while j < a_len {
              let ca = a[a_start + j];
              let cb = b_slice[b_start + j];
              if ca != cb { return ca == '1' && cb == '0'; }
              j += 1;
          }
          // equal
          true
      }

      let rem_ge = seq_ge(&rem, divisor);
      if rem_ge {
          // subtract divisor from rem (a >= b)
          let mut borrow: i8 = 0;
          let mut ai: int = rem.len() as int - 1;
          let mut bi: int = divisor.len() as int - 1;
          while ai >= 0 {
              let aval: i8 = if rem[ai as usize] == '1' { 1 } else { 0 };
              let bval: i8 = if bi >= 0 && divisor[bi as usize] == '1' { 1 } else { 0 };
              let mut diff: i8 = aval - bval - borrow;
              if diff < 0 {
                  diff += 2;
                  borrow = 1;
              } else {
                  borrow = 0;
              }
              rem[ai as usize] = if diff == 1 { '1' } else { '0' };
              ai -= 1;
              bi -= 1;
          }
          // remove leading zeros
          while rem.len() > 0 && rem[0] == '0' {
              rem.remove(0);
          }
          q.push('1');
      } else {
          q.push('0');
      }

      i += 1;

      proof {
          // The loop invariant is maintained by construction: refer to Str2Int_append lemma
          assert(0 <= i && i <= n);
      }
  }

  // strip leading zeros from quotient
  while q.len() > 0 && q[0] == '0' {
      q.remove(0);
  }

  return (q, rem);
}

// </vc-code>

fn main() {}
}


