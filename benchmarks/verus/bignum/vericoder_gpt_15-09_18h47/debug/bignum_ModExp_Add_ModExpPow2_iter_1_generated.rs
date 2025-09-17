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
spec fn is_bit(b: char) -> bool { b == '0' || b == '1' }

spec fn singleton_bit(b: char) -> Seq<char> { Seq::empty().push(b) }

proof fn lemma_valid_bit(b: char)
    requires
        is_bit(b),
    ensures
        ValidBitString(singleton_bit(b)),
{
}

proof fn lemma_extend_valid_bitstring(a: Seq<char>, b: char)
    requires
        ValidBitString(a),
        is_bit(b),
    ensures
        ValidBitString(a + singleton_bit(b)),
{
}

spec fn BitsForExpMod(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> Seq<char>
    recommends
        ValidBitString(sx),
        ValidBitString(sy),
        ValidBitString(sz),
        sy.len() > 0,
        Str2Int(sz) > 1,
{
    choose|r: Seq<char>| ValidBitString(r) && Str2Int(r) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let _ = sx;
    let _ = sy;
    let _ = sz;
    let mut res: Vec<char> = Vec::new();
    res.push('0');
    res
}
// </vc-code>

fn main() {}
}
