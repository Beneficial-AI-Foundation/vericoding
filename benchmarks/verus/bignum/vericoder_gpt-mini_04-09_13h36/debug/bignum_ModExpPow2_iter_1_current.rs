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
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
exec fn nat_to_bits(v: nat) -> (res: Vec<char>)
  ensures Str2Int(res@) == v,
          ValidBitString(res@)
  decreases v
{
  if v == 0 {
    return Vec::<char>::new();
  } else {
    let mut prefix = nat_to_bits(v / 2);
    let b = if v % 2 == 1 { '1' } else { '0' };
    // capture old prefix sequence for reasoning
    let old_prefix_seq = prefix@;
    prefix.push(b);
    proof {
      // length increased by one
      assert(prefix@.len() as int == old_prefix_seq.len() as int + 1);
      // the subrange excluding last element equals old prefix
      assert(prefix@.subrange(0, prefix@.len() as int - 1) == old_prefix_seq);
      // bit value
      let bitval: nat = if b == '1' { 1 } else { 0 };
      // By definition of Str2Int on non-empty seq
      assert(Str2Int(prefix@) == 2 * Str2Int(old_prefix_seq) + bitval);
      // From recursive call
      assert(Str2Int(old_prefix_seq) == v / 2);
      assert(bitval == v % 2);
      assert(2 * (v / 2) + (v % 2) == v);
      assert(Str2Int(prefix@) == v);
      assert(ValidBitString(prefix@));
    }
    return prefix;
  }
}

proof fn Exp_int_mul(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
    // a + 0 == a, Exp_int(x,0) == 1
    assert(Exp_int(x, a + 0) == Exp_int(x, a));
    assert(Exp_int(x, 0) == 1);
    assert(Exp_int(x, a) * Exp_int(x, 0) == Exp_int(x, a));
  } else {
    // b >= 1
    Exp_int_mul(x, a, b - 1);
    // Expand definitions:
    // Exp_int(x, a + b) = x * Exp_int(x, a + b - 1)
    // Exp_int(x, b) = x * Exp_int(x, b - 1)
    assert(Exp_int(x, a + b) == x * Exp_int(x, a + b - 1));
    assert(Exp_int(x, b) == x * Exp_int(x, b - 1));
    // By inductive hypothesis Exp_int(x, a + b - 1) == Exp_int(x, a) * Exp_int(x, b - 1)
    assert(Exp_int(x, a + b - 1) == Exp_int(x, a) * Exp_int(x, b - 1));
    // Combine
    assert(Exp_int(x, a + b) == x * (Exp_int(x, a) * Exp_int(x, b - 1)));
    assert(x * (Exp_int(x, a) * Exp_int(x, b - 1)) == Exp_int(x, a) * (x * Exp_int(x
// </vc-helpers>

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
exec fn nat_to_bits(v: nat) -> (res: Vec<char>)
  ensures Str2Int(res@) == v,
          ValidBitString(res@)
  decreases v
{
  if v == 0 {
    return Vec::<char>::new();
  } else {
    let mut prefix = nat_to_bits(v / 2);
    let b = if v % 2 == 1 { '1' } else { '0' };
    // capture old prefix sequence for reasoning
    let old_prefix_seq = prefix@;
    prefix.push(b);
    proof {
      // length increased by one
      assert(prefix@.len() as int == old_prefix_seq.len() as int + 1);
      // the subrange excluding last element equals old prefix
      assert(prefix@.subrange(0, prefix@.len() as int - 1) == old_prefix_seq);
      // bit value
      let bitval: nat = if b == '1' { 1 } else { 0 };
      // By definition of Str2Int on non-empty seq
      assert(Str2Int(prefix@) == 2 * Str2Int(old_prefix_seq) + bitval);
      // From recursive call
      assert(Str2Int(old_prefix_seq) == v / 2);
      assert(bitval == v % 2);
      assert(2 * (v / 2) + (v % 2) == v);
      assert(Str2Int(prefix@) == v);
      assert(ValidBitString(prefix@));
    }
    return prefix;
  }
}

proof fn Exp_int_mul(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  if b == 0 {
    // a + 0 == a, Exp_int(x,0) == 1
    assert(Exp_int(x, a + 0) == Exp_int(x, a));
    assert(Exp_int(x, 0) == 1);
    assert(Exp_int(x, a) * Exp_int(x, 0) == Exp_int(x, a));
  } else {
    // b >= 1
    Exp_int_mul(x, a, b - 1);
    // Expand definitions:
    // Exp_int(x, a + b) = x * Exp_int(x, a + b - 1)
    // Exp_int(x, b) = x * Exp_int(x, b - 1)
    assert(Exp_int(x, a + b) == x * Exp_int(x, a + b - 1));
    assert(Exp_int(x, b) == x * Exp_int(x, b - 1));
    // By inductive hypothesis Exp_int(x, a + b - 1) == Exp_int(x, a) * Exp_int(x, b - 1)
    assert(Exp_int(x, a + b - 1) == Exp_int(x, a) * Exp_int(x, b - 1));
    // Combine
    assert(Exp_int(x, a + b) == x * (Exp_int(x, a) * Exp_int(x, b - 1)));
    assert(x * (Exp_int(x, a) * Exp_int(x, b - 1)) == Exp_int(x, a) * (x * Exp_int(x
// </vc-code>

fn main() {}
}