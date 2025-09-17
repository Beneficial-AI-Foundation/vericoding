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
exec fn Nat2Vec(n: nat) -> Vec<char>
  ensures ValidBitString(result@),
          Str2Int(result@) == n
  decreases n
{
    if n == 0 {
        Vec::new()
    } else {
        let mut v = Nat2Vec(n / 2);
        let ch: char = if n % 2 == 1 { '1' } else { '0' };
        v.push(ch);
        proof {
            let len = v.len() as int;
            assert(len > 0);
            assert(v@[len - 1] == ch);
            assert(Str2Int(v@) == 2 * Str2Int(v@.subrange(0, len - 1))
                   + (if v@[len - 1] == '1' { 1 } else { 0 }));
            assert(Str2Int(v@.subrange(0, len - 1)) == n / 2);
            assert((if v@[len - 1] == '1' { 1 } else { 0 }) == n % 2);
            assert(2 * (n / 2) + n % 2 == n);
        }
        v
    }
}

exec fn Slice2Nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let k_int: int = s.len() as int;
        let ch: char = s[(k_int - 1) as usize];
        let bit: nat = if ch == '1' { 1 } else { 0 };
        let prefix = &s[0..(k_int - 1) as usize];
        let n_prefix = Slice2Nat(prefix);
        proof {
            // relate runtime indexing to sequence view
            assert((&s)@[k_int - 1] == ch);
            // by recursive postcondition
            assert(n_prefix == Str2Int(prefix@));
            // relation of whole string to prefix
            assert(Str2Int(s@) ==
                   2 * Str2Int(s@.subrange(0, k_int - 1))
                   + (if s@[k_int - 1] == '1' { 1 } else { 0 }));
            // prefix@ equals s@.subrange(0, k_int - 1)
            assert(prefix@ == s@.subrange(0, k_int - 1));
            // combine equalities
            assert(2 * Str2Int(prefix@) + (if ch == '1' { 1 } else { 0 })
                   == Str2Int(s@));
            assert((if ch == '1' { 1 } else { 0 }) == bit);
            assert(2 * n_prefix + bit == Str2Int(s@));
        }
        2 * n_prefix + bit
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1: nat = Slice2Nat(s1);
    let n2: nat = Slice2Nat(s2);
    let prod: nat = n1 * n2;
    Nat2Vec(prod)
}
// </vc-code>

fn main() {}
}