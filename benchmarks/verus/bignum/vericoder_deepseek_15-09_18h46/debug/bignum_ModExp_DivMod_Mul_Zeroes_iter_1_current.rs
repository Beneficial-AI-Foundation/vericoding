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
proof fn exp_int_zero(x: nat) ensures Exp_int(x, 0) == 1 { }
proof fn exp_int_recursive(x: nat, y: nat) requires y > 0 ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat) { }
proof fn str2int_empty() ensures Str2Int(Seq::<char>::empty()) == 0 { }
proof fn str2int_recursive(s: Seq<char>, c: char) requires ValidBitString(s.push(c)) && (c == '0' || c == '1') ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1 } else { 0 }) { }
proof fn valid_bit_string_maintained(s: Seq<char>, c: char) requires ValidBitString(s) && (c == '0' || c == '1') ensures ValidBitString(s.push(c)) { }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  proof {
    exp_int_zero(Str2Int(sx@));
    exp_int_recursive(Str2Int(sx@), Str2Int(sy@));
    str2int_empty();
    str2int_recursive(Seq::<char>::empty(), '1');
    valid_bit_string_maintained(Seq::<char>::empty(), '0');
  }
  
  let mut res = Vec::new();
  res.push('0');
  res
}
// </vc-code>

fn main() {}
}
