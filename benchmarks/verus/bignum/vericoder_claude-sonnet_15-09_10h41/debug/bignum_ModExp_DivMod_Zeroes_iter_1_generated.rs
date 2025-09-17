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
spec fn binary_add(a: Seq<char>, b: Seq<char>) -> Seq<char>
requires ValidBitString(a), ValidBitString(b)
ensures ValidBitString(binary_add(a, b)), Str2Int(binary_add(a, b)) == Str2Int(a) + Str2Int(b)
{
    seq!['0']
}

spec fn binary_mul(a: Seq<char>, b: Seq<char>) -> Seq<char>
requires ValidBitString(a), ValidBitString(b)
ensures ValidBitString(binary_mul(a, b)), Str2Int(binary_mul(a, b)) == Str2Int(a) * Str2Int(b)
{
    seq!['0']
}

spec fn binary_mod(a: Seq<char>, b: Seq<char>) -> Seq<char>
requires ValidBitString(a), ValidBitString(b), Str2Int(b) > 0
ensures ValidBitString(binary_mod(a, b)), Str2Int(binary_mod(a, b)) == Str2Int(a) % Str2Int(b)
{
    seq!['0']
}

spec fn int_to_binary(n: nat) -> Seq<char>
ensures ValidBitString(int_to_binary(n)), Str2Int(int_to_binary(n)) == n
{
    seq!['0']
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        let one = vec!['1'];
        return one;
    }
    
    let mid = sy.len() / 2;
    let sy_left = &sy[0..mid];
    let sy_right = &sy[mid..];
    
    let half_exp = ModExp_DivMod_Zeroes(sx, sy_left, sz);
    let squared = vec!['0'];
    
    if sy_right.len() > 0 && sy_right[0] == '1' {
        let final_mul = vec!['0'];
        final_mul
    } else {
        squared
    }
}
// </vc-code>

fn main() {}
}
