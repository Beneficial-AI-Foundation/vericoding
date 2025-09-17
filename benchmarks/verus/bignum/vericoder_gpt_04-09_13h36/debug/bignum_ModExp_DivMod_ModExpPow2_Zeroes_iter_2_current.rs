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
    let s
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
    let s
// </vc-code>

fn main() {}
}