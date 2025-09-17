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
    // Use associativity: x * (A * B) == (x * A) * B
    assert(x * (Exp_int(x, a) * Exp_int(x, b - 1)) == (x * Exp_int(x, a)) * Exp_int(x, b - 1));
    // Use commutativity for the middle product: x * Exp_int(x, a) == Exp_int(x, a) * x
    assert(x * Exp_int(x, a) == Exp_int(x, a) * x);
    assert((x * Exp_int(x, a)) * Exp_int(x, b - 1) == (Exp_int(x, a) * x) * Exp_int(x, b - 1));
    // Re-associate to get Exp_int(x, a) * (x * Exp_int(x, b - 1))
    assert((Exp_int(x, a) * x) * Exp_int(x, b - 1) == Exp_int(x, a) * (x * Exp_int(x, b - 1)));
    // And x * Exp_int(x, b - 1) == Exp_int(x, b)
    assert(x * Exp_int(x, b - 1) == Exp_int(x, b));
    // Conclude
    assert(Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b));
  }
}
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
{
  let base: nat = Str2Int(sx@);
  let exp: nat = Str2Int(sy@);
  let m: nat = Str2Int(sz@);

  if exp == 0 {
    // base^0 == 1
    let out = nat_to_bits(1 % m);
    return out;
  } else {
    // exp == Exp_int(2, n)
    // Initialize r = base % m, and iterate n times squaring to get base^{2^n} % m
    let mut r: nat = base % m;
    let mut i: int = 0;

    // Establish initial invariant: r == base^{2^0} % m == base % m
    proof {
      assert(i == 0);
      assert(Exp_int(2, 0) == 1);
      assert(Exp_int(base, Exp_int(2, 0)) == Exp_int(base, 1));
      assert(Exp_int(base, 1) == base * Exp_int(base, 0));
      assert(Exp_int(base, 0) == 1);
      assert(Exp_int(base, 1) == base);
      assert(r == base % m);
    }

    while i < n
      invariant 0 <= i && i <= n,
                r < m,
                // r is congruent to base^{2^i} modulo m
                r == Exp_int(base, Exp_int(2, i as nat)) % m
    {
      let old_i = i;
      let old_r = r;
      // square modulo m
      r = (r * r) % m;
      i = i + 1;

      proof {
        // From the invariant before the update:
        assert(old_r == Exp_int(base, Exp_int(2, old_i as nat)) % m);
        // Let e = Exp_int(2, old_i)
        let e: nat = Exp_int(2, old_i as nat);
        // Use lemma to get Exp_int(base, e + e) == Exp_int(base, e) * Exp_int(base, e)
        Exp_int_mul(base, e, e);
        assert(Exp_int(base, e + e) == Exp_int(base, e) * Exp_int(base, e));
        // Relate Exp_int(2, old_i + 1) to 2 * Exp_int(2, old_i)
        assert(Exp_int(2, (old_i as nat) + 1) == 2 * Exp_int(2, old_i as nat));
        assert(2 * Exp_int(2, old_i as nat) == Exp_int(2, old_i as nat) + Exp_int(2, old_i as nat));
        // Combine to get equality of exponents:
        assert(Exp_int(base, Exp_int(2, (old_i as nat) + 1)) ==
               Exp_int(base, Exp_int(2, old_i as nat) + Exp_int(2, old_i as nat)));
        // Now reason about modulo: old_r == Exp_int(base,e) % m, so (old_r*old_r)%m == (Exp_int(base,e)*Exp_int(base,e))%m
        assert((old_r * old_r) % m == (Exp_int(base, Exp_int(2, old_i as nat)) * Exp_int(base, Exp_int(2, old_i as nat))) % m);
        // Using above equalities, conclude new r equals required value modulo m
        assert(r == Exp_int(base, Exp_int(2, (old_i as nat) + 1)) % m);
        // bounds: after modulo, r < m holds
        assert(r < m);
      }
    }

    // After loop, i == n and r == base^{2^n} % m == base^{exp} % m
    // Return bits for r
    let out = nat_to_bits(r);
    return out;
  }
}
// </vc-code>

fn main() {}
}