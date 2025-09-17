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

exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
{
  assume(false);
  return Vec::<char>::new();
}

exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
{
  assume(false);
  return (Vec::<char>::new(), Vec::<char>::new());
}

exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
{
  assume(false);
  return Vec::<char>::new();
}

// <vc-helpers>
/* helper modified by LLM (iteration 5): used split_at to fix compilation error with slicing */
exec fn MulMod(sa: &[char], sb: &[char], sm: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(sa@),
        ValidBitString(sb@),
        ValidBitString(sm@),
        Str2Int(sm@) > 0,
    ensures
        ValidBitString(res@),
        Str2Int(res@) == (Str2Int(sa@) * Str2Int(sb@)) % Str2Int(sm@),
    decreases sb.len()
{
    if sb.len() == 0 {
        return Vec::new();
    }

    let (sb_prefix, last_char_slice) = sb.split_at(sb.len() - 1);
    let last_bit_is_one = last_char_slice[0] == '1';

    let rec_res = MulMod(sa, sb_prefix, sm);

    let rec_res_doubled = Add(&rec_res, &rec_res);
    let term = DivMod(&rec_res_doubled, sm).1;

    if last_bit_is_one {
        let sa_mod = DivMod(sa, sm).1;
        let final_res_unmod = Add(&term, &sa_mod);
        let final_res = DivMod(&final_res_unmod, sm).1;
        final_res
    } else {
        term
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): used split_at to fix compilation error with slicing */
{
    let y_len = sy.len();
    if y_len == 1 {
        if sy[0] == '0' {
            let mut res = Vec::new();
            res.push('1');
            return res;
        } else {
            let (_q, rem) = DivMod(sx, sz);
            return rem;
        }
    }

    let (sy_prefix, last_char_slice) = sy.split_at(y_len - 1);
    let last_char = last_char_slice[0];

    let sx_squared_mod_z = MulMod(sx, sx, sz);

    let res_rec = ModExp(&sx_squared_mod_z, sy_prefix, sz);

    if last_char == '0' {
        return res_rec;
    } else {
        let sx_mod_z = DivMod(sx, sz).1;
        let final_res = MulMod(&res_rec, &sx_mod_z, sz);
        return final_res;
    }
}
// </vc-code>

fn main() {}
}
