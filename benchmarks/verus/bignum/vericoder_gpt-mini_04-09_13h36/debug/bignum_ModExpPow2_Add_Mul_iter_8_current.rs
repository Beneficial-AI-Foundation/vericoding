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
    assert(NatToBits(0) == Seq::empty::<char>());
    assert(Str2Int(NatToBits(0)) == 0nat);
    assert(ValidBitString(NatToBits(0)));
  } else {
    let q = n / 2;
    let r = n % 2;
    nat_to_bits_prop(q);
    assert(Str2Int(NatToBits(q)) == q);
    assert(ValidBitString(NatToBits(q)));
    let bit = if r == 1 { '1' } else { '0' };
    let t = NatToBits(q).concat(seq![bit]);
    let last_idx: int = t.len() as int - 1;
    assert(t.subrange(0, last_idx) == NatToBits(q));
    assert(t.index(last_idx) == bit);
    // unfold Str2Int for non-empty t
    assert(Str2Int(t) == 2 * Str2Int(t.subrange(0, last_idx)) + (if t.index(last_idx) == '1' { 1nat } else { 0nat }));
    assert(Str2Int(t) == 2 * Str2Int(NatToBits(q)) + (if bit == '1' { 1nat } else { 0nat }));
    assert((if bit == '1' { 1nat } else { 0nat }) == r);
    assert(2 * Str2Int(NatToBits(q)) + r == 2 * q + r);
    assert(n == 2 * q + r);
    assert(Str2Int(NatToBits(n)) == n);
    assert(ValidBitString(t));
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
  proof {
    nat_to_bits_prop(sum);
    assert(Str2Int(NatToBits(sum)) == sum);
    assert(ValidBitString(NatToBits(sum)));
  }
  return Vec::from_seq(NatToBits(sum));
}
// </vc-code>

fn main() {}
}