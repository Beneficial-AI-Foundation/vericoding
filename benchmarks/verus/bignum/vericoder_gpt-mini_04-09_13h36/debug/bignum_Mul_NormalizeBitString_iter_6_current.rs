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
// Helper spec: sum of bits treating index 0 as least-significant (weight 2^0)
spec fn BitSum(b: Seq<char>) -> nat
  decreases b.len()
{
    if b.len() == 0 {
        0
    } else {
        2 * BitSum(b.subrange(1, b.len() as int)) + (if b.index(0) == '1' { 1 } else { 0 })
    }
}

// Execute: convert slice of chars (MSB..LSB) to nat according to Str2Int
exec fn seq_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures seq_to_nat(s) == Str2Int(s@)
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let n = s.len();
        let last = s[n - 1];
        let prefix = &s[0..(n - 1)];
        let pref_val = seq_to_nat(prefix);
        if last == '1' {
            2 * pref_val + 1
        } else {
            2 * pref_val
        }
    }
}

// Execute: convert nat to Vec<char> representing bits MSB..LSB such that Str2Int(seq) == n
exec fn nat_to_seq(n: nat) -> (result: Vec<char>)
  ensures ValidBitString(result@) && Str2Int(result@) == n
  decreases n
{
    if n == 0 {
        Vec::new()
    } else {
        let b = if n % 2 == 1 { '1' } else { '0' };
        let mut v = nat_to_seq(n / 2);
        let old_seq = v@;
        v.push(b);
        proof {
            // From recursive call
            assert(Str2Int(old_seq) == n / 2);
            assert( if b == '1' { 1 } else { 0 } == (n % 2) );
            // By definition of Str2Int on the pushed vector: last element is the bit b
            assert(Str2Int(v@) ==
                   2 * Str2Int(v@.subrange(0, v.len() as int - 1)) +
                   (if v@.index(v.len() as int - 1) == '1' { 1 } else { 0 }));
            // v@.subrange(0, v.len()-1) == old_seq
            assert(v@.subrange(0, v.len() as int - 1) == old_seq);
            // last char equals b
            assert(v@.index(v.len() as int - 1) == b);
            // Combine
            assert(Str2Int(v@) == 2 * Str2Int(old_seq) + (if b == '1' { 1 } else { 0 }));
            // Use arithmetic identity: n == 2*(n/2) + (n%2)
            assert(n == 2 * (n / 2) + (n % 2));
            assert(Str2Int(v@) == n);
            // ValidBitString: old_seq had ValidBitString, and b is '0' or '1'
            assert(ValidBitString(old_seq));
            assert(b == '0' || b == '1');
            // Therefore new sequence is valid
            assert(forall |i: int| 0 <= i && i < v.len() as int ==>
                (v@.index(i) == '0' || v@.index(i) == '1'));
        }
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  let n1 = seq_to_nat(s1);
  let n2 = seq_to_nat(s2);
  let prod = n1 * n2;
  let res = nat_to_seq(prod);
  res
}
// </vc-code>

fn main() {}
}