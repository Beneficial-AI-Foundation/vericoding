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

// <vc-helpers>
spec fn NatToBits(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    Seq::empty()
  } else {
    let q = n / 2;
    let r = n % 2;
    let bit = if r == 1 { '1' } else { '0' };
    NatToBits(q).concat(seq![bit])
  }
}

proof fn nat_to_bits_prop(n: nat)
  ensures Str2Int(NatToBits(n)) == n
  ensures ValidBitString(NatToBits(n))
  decreases n
{
  if n == 0 {
    // Str2Int(Seq::empty()) == 0 by definition
    assert(Str2Int(NatToBits(0)) == 0);
    assert(ValidBitString(NatToBits(0)));
  } else {
    let q = n / 2;
    let r = n % 2;
    nat_to_bits_prop(q);
    proof {
      assert(Str2Int(NatToBits(q)) == q);
      assert(ValidBitString(NatToBits(q)));
      let bit = if r == 1 { '1' } else { '0' };
      // For s = NatToBits(q).concat(seq![bit]), by the definition of Str2Int on non-empty sequences:
      // Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len()-1)) + (if s.index(s.len()-1) == '1' {1} else {0})
      // Here s.subrange(0, s.len()-1) == NatToBits(q) and s.index(s.len()-1) == bit.
      assert(Str2Int(NatToBits(q).concat(seq![bit])) == 2 * Str2Int(NatToBits(q)) + (if bit == '1' { 1 } else { 0 }));
      // Replace Str2Int(NatToBits(q)) with q by induction hypothesis
      assert(2 * Str2Int(NatToBits(q)) + (if bit == '1' { 1 } else { 0 }) == 2 * q + r);
      // Division/modulo decomposition: n == 2*q + r
      assert(n == 2 * q + r);
      // Chain equalities to conclude Str2Int(NatToBits(n)) == n
      assert(Str2Int(NatToBits(n)) == n);
      // ValidBitString: concat of valid bits with a single '0'/'1' is valid
      assert(ValidBitString(NatToBits(n)));
    }
  }
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  let n1: nat = Str2Int(s1@);
  let n2: nat = Str2Int(s2@);
  let sum: nat = n1 + n2;
  let bits: Seq<char> = NatToBits(sum);
  proof {
    // establish the required facts about bits
    nat_to_bits_prop(sum);
    assert(Str2Int(bits) == sum);
    assert(ValidBitString(bits));
  }
  return Vec::from_seq(bits);
}
// </vc-code>

fn main() {}
}