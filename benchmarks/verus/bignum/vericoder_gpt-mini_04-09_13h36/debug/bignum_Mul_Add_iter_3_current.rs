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
exec fn Nat2Vec(n: usize) -> Vec<char>
  ensures ValidBitString(result@),
          Str2Int(result@) == (n as nat)
  decreases n
{
    if n == 0 {
        Vec::new()
    } else {
        let mut v = Nat2Vec(n / 2);
        let ch: char = if n % 2 == 1 { '1' } else { '0' };
        v.push(ch);
        proof {
            let len: int = v.len() as int;
            assert(len > 0);
            assert(v@[len - 1] == ch);
            assert(Str2Int(v@) == 2 * Str2Int(v@.subrange(0, len - 1))
                   + (if v@[len - 1] == '1' { 1 } else { 0 }));
            assert(Str2Int(v@.subrange(0, len - 1)) == ((n / 2) as nat));
            assert((if v@[len - 1] == '1' { 1 } else { 0 }) == ((n % 2) as nat));
            assert(2 * ((n / 2) as nat) + ((n % 2) as nat) == (n as nat));
        }
        v
    }
}

exec fn Slice2Nat(s: &[char]) -> usize
  requires ValidBitString(s@)
  ensures (result as nat) == Str2Int(s@)
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let k: usize = s.len();
        let ch: char = s[k - 1];
        let bit: usize = if ch == '1' { 1 } else { 0 };
        let prefix = &s[0..k - 1];
        let n_prefix = Slice2Nat(prefix);
        proof {
            let k_int: int = k as int;
            // relate runtime indexing to sequence view
            assert((&s)@[k_int - 1] == ch);
            // by recursive postcondition (cast)
            assert((n_prefix as nat) == Str2Int(prefix@));
            // relation of whole string to prefix
            assert(Str2Int(s@) ==
                   2 * Str2Int(s@.subrange(0, k_int - 1))
                   + (if s@[k_int - 1] == '1' { 1 } else { 0 }));
            // prefix@ equals s@.subrange(0, k_int - 1)
            assert(prefix@ == s@.subrange(0, k_int - 1));
            // combine equalities
            assert(2 * (n_prefix as nat) + (if ch == '1' { 1 } else { 0 })
                   == Str2Int(s@));
            assert((if ch == '1' { 1usize } else { 0usize }) == bit);
            assert(2usize * n_prefix + bit == (Str2Int(s@) as usize));
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
    let n1: usize = Slice2Nat(s1);
    let n2: usize = Slice2Nat(s2);
    let prod: usize = n1 * n2;
    let res: Vec<char> = Nat2Vec(prod);
    proof {
        // relate runtime values to specifications
        assert((n1 as nat) == Str2Int(s1@));
        assert((n2 as nat) == Str2Int(s2@));
        assert((prod as nat) == (n1 as nat) * (n2 as nat));
        // Nat2Vec postcondition
        assert(Str2Int(res@) == (prod as nat));
    }
    res
}
// </vc-code>

fn main() {}
}