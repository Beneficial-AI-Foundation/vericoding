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
proof fn lemma_validbit_push(s: Seq<char>, c: char)
  requires
    ValidBitString(s),
    c == '0' || c == '1'
  ensures
    ValidBitString(s.push(c))
{
  assert forall |i: int| 0 <= i && i < s.push(c).len() as int
    implies s.push(c).index(i) == '0' || s.push(c).index(i) == '1' by {
    if i < s.len() as int {
      assert(s.push(c).index(i) == s.index(i));
      assert(ValidBitString(s));
    } else {
      assert(i == s.len() as int);
      assert(s.push(c).index(i) == c);
    }
  }
}

proof fn lemma_exists_bitstring(n: nat)
  ensures exists |s: Seq<char>| ValidBitString(s) && Str2Int(s) == n
  decreases n
{
  if n == 0 {
    let s = Seq::<char>::empty();
    assert(ValidBitString(s));
    assert(Str2Int(s) == 0);
    assert(exists |t: Seq<char>| ValidBitString(t) && Str2Int(t) == n) by {
      assert(ValidBitString(s) && Str2Int(s) == n);
    }
  } else {
    let r: int = n % 2;
    let q: int = n / 2;
    assert(0 <= r && r < 2);
    assert(0 <= q);
    let m: nat = q as nat;
    lemma_exists_bitstring(m);
    let s0 = choose |s: Seq<char>| ValidBitString(s) && Str2Int(s) == m;

    let b: char = if r == 1 { '1' } else { '0' };

    // Validity after push
    lemma_validbit_push(s0, b);

    let sp = s0.push(b);
    let l: int = sp.len() as int;
    assert(l == s0.len() as int + 1);
    assert(l > 0);

    // Show prefix of sp (all but last) equals s0
    assert(sp.subrange(0, l - 1).len() == s0.len());
    assert forall |i: int|
      0 <= i && i < s0.len() as int
      implies sp.subrange(0, l - 1).index(i) == s0.index(i) by
    {
      assert(sp.subrange(0, l - 1).index(i) == sp.index(i));
      assert(sp.index(i) == s0.index(i));
    }
    assert(sp.subrange(0, l - 1) =~= s0);

    // Last element is b
    assert(sp.index(l - 1) == b);

    // Compute Str2Int(sp) via definition
    let bit_val: nat = if b == '1' { 1nat } else { 0nat };
    assert(Str2Int(sp) == 2 * Str2Int(sp.subrange(0, l - 1
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
proof fn lemma_validbit_push(s: Seq<char>, c: char)
  requires
    ValidBitString(s),
    c == '0' || c == '1'
  ensures
    ValidBitString(s.push(c))
{
  assert forall |i: int| 0 <= i && i < s.push(c).len() as int
    implies s.push(c).index(i) == '0' || s.push(c).index(i) == '1' by {
    if i < s.len() as int {
      assert(s.push(c).index(i) == s.index(i));
      assert(ValidBitString(s));
    } else {
      assert(i == s.len() as int);
      assert(s.push(c).index(i) == c);
    }
  }
}

proof fn lemma_exists_bitstring(n: nat)
  ensures exists |s: Seq<char>| ValidBitString(s) && Str2Int(s) == n
  decreases n
{
  if n == 0 {
    let s = Seq::<char>::empty();
    assert(ValidBitString(s));
    assert(Str2Int(s) == 0);
    assert(exists |t: Seq<char>| ValidBitString(t) && Str2Int(t) == n) by {
      assert(ValidBitString(s) && Str2Int(s) == n);
    }
  } else {
    let r: int = n % 2;
    let q: int = n / 2;
    assert(0 <= r && r < 2);
    assert(0 <= q);
    let m: nat = q as nat;
    lemma_exists_bitstring(m);
    let s0 = choose |s: Seq<char>| ValidBitString(s) && Str2Int(s) == m;

    let b: char = if r == 1 { '1' } else { '0' };

    // Validity after push
    lemma_validbit_push(s0, b);

    let sp = s0.push(b);
    let l: int = sp.len() as int;
    assert(l == s0.len() as int + 1);
    assert(l > 0);

    // Show prefix of sp (all but last) equals s0
    assert(sp.subrange(0, l - 1).len() == s0.len());
    assert forall |i: int|
      0 <= i && i < s0.len() as int
      implies sp.subrange(0, l - 1).index(i) == s0.index(i) by
    {
      assert(sp.subrange(0, l - 1).index(i) == sp.index(i));
      assert(sp.index(i) == s0.index(i));
    }
    assert(sp.subrange(0, l - 1) =~= s0);

    // Last element is b
    assert(sp.index(l - 1) == b);

    // Compute Str2Int(sp) via definition
    let bit_val: nat = if b == '1' { 1nat } else { 0nat };
    assert(Str2Int(sp) == 2 * Str2Int(sp.subrange(0, l - 1
// </vc-code>

fn main() {}
}