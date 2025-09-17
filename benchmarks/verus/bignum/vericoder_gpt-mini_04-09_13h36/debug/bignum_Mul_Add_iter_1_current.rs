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
            // len > 0 because we just pushed
            assert(len > 0);
            // last character equals ch
            assert(v@[len - 1] == ch);
            // By definition of Str2Int on a non-empty sequence:
            assert(Str2Int(v@) == 2 * Str2Int(v@.subrange(0, len - 1))
                   + (if v@[len - 1] == '1' { 1 } else { 0 }));
            // From recursive call: Str2Int(v@.subrange(0, len - 1)) == n / 2
            assert(Str2Int(v@.subrange(0, len - 1)) == n / 2);
            // The last bit equals n % 2
            assert((if v@[len - 1] == '1' { 1 } else { 0 }) == n % 2);
            // arithmetic identity
            assert(2 * (n / 2) + n % 2 == n);
        }
        v
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    // compute n1 = Str2Int(s1@)
    let mut i: int = 0;
    let len1: int = s1.len() as int;
    let mut n1: nat = 0;
    while i < len1
        invariant 0 <= i && i <= len1
        invariant n1 == Str2Int(s1@.subrange(0, i))
        decreases len1 - i
    {
        let old_n1 = n1;
        let ch: char = s1[i as usize];
        let bit: nat = if ch == '1' { 1 } else { 0 };
        n1 = 2 * old_n1 + bit;
        i += 1;
        proof {
            let k = i;
            // character at position k-1 is ch
            assert(s1@[k - 1] == ch);
            // by Str2Int definition on prefix of length k
            assert(Str2Int(s1@.subrange(0, k)) ==
                   2 * Str2Int(s1@.subrange(0, k - 1))
                   + (if s1@[k - 1] == '1' { 1 } else { 0 }));
            // from the invariant before update: old_n1 == Str2Int(s1@.subrange(0, k-1))
            assert(Str2Int(s1@.subrange(0, k - 1)) == old_n1);
            // bit matches the character
            assert((if s1@[k - 1] == '1' { 1 } else { 0 }) == bit);
            // conclude new n1 equals Str2Int of prefix length k
            assert(n1 == Str2Int(s1@.subrange(0, k)));
        }
    }

    // compute n2 = Str2Int(s2@)
    let mut j: int = 0;
    let len2: int = s2.len() as int;
    let mut n2: nat = 0;
    while j < len2
        invariant 0 <= j && j <= len2
        invariant n2 == Str2Int(s2@.subrange(0, j))
        decreases len2 - j
    {
        let old_n2 = n2;
        let ch2: char = s2[j as usize];
        let bit2: nat = if ch2 == '1' { 1 } else { 0 };
        n2 = 2 * old_n2 + bit2;
        j += 1;
        proof {
            let k = j;
            assert(s2@[k - 1] == ch2);
            assert(Str2Int(s2@.subrange(0, k)) ==
                   2 * Str2Int(s2@.subrange(0, k - 1))
                   + (if s2@[k - 1] == '1' { 1 } else { 0 }));
            assert(Str2Int(s2@.subrange(0, k - 1)) == old_n2);
            assert((if s2@[k - 1] == '1' { 1 } else { 0 }) == bit2);
            assert(n2 == Str2Int(s2@.subrange(0, k)));
        }
    }

    // product
    let prod: nat = n1 * n2;

    // convert product to bitstring (MSB-first) and return
    Nat2Vec(prod)
}
// </vc-code>

fn main() {}
}