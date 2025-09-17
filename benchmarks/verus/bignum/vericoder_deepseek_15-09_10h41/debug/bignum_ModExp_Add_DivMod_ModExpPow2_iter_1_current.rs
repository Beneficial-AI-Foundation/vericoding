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

proof fn mod_exp_helper_lemma(x: nat, y: nat, z: nat) 
    requires z > 1
    ensures Exp_int(x, y) % z == Exp_int(x % z, y) % z
{
    if y == 0 {
        assert(Exp_int(x, 0) == 1);
        assert(Exp_int(x % z, 0) == 1);
        assert(1 % z == if 1 < z { 1 } else { 0 });
    } else {
        mod_exp_helper_lemma(x, y - 1, z);
        assert(Exp_int(x, y) == x * Exp_int(x, y - 1));
        assert(Exp_int(x % z, y) == (x % z) * Exp_int(x % z, y - 1));
        assert((x * Exp_int(x, y - 1)) % z == ((x % z) * (Exp_int(x, y - 1) % z)) % z);
    }
}

proof fn divmod_helper_lemma(dividend: nat, divisor: nat)
    requires divisor > 0
    ensures dividend / divisor == (dividend % divisor == 0 ? dividend / divisor : dividend / divisor)
{
}

proof fn valid_bitstring_lemma(s: Seq<char>)
    requires ValidBitString(s)
    ensures forall |i: int| 0 <= i && i < s.len() ==> (s[i] == '0' || s[i] == '1')
{
}

proof fn str2int_nonnegative_lemma(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
{
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
{
    if sy@.len() == 1 {
        if sy@[0] == '0' {
            let base = Exp_int(Str2Int(sx@), 0) % Str2Int(sz@);
            let result: Vec<char> = Vec::new();
            if base == 0 {
                result.push('0');
            } else if base == 1 {
                result.push('1');
            }
            return result;
        } else {
            let base = Exp_int(Str2Int(sx@), 1) % Str2Int(sz@);
            let result: Vec<char> = Vec::new();
            if base == 0 {
                result.push('0');
            } else if base == 1 {
                result.push('1');
            }
            return result;
        }
    } else {
        let n = sy@.len() - 1;
        let (div, rem) = DivMod(sy, &['0', '1']);
        let pow2_result = ModExpPow2(sx, &div@, n, sz);
        if rem@[0] == '1' {
            let temp = (Str2Int(pow2_result@) * Str2Int(sx@)) % Str2Int(sz@);
            let result: Vec<char> = Vec::new();
            if temp == 0 {
                result.push('0');
            } else if temp == 1 {
                result.push('1');
            }
            return result;
        } else {
            return pow2_result;
        }
    }
}
// </vc-code>

fn main() {}
}
