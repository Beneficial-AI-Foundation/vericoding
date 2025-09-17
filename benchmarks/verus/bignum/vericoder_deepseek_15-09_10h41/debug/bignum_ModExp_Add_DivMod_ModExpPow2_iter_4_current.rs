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
proof fn divmod_helper_lemma(dividend: nat, divisor: nat)
    requires divisor > 0
    ensures dividend / divisor == (if dividend % divisor == 0 { dividend / divisor } else { dividend / divisor })
{
    assert(dividend / divisor == dividend / divisor);
}

proof fn nat_to_bitstring_lemma(val: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@) && Str2Int(res@) == val
{
    if val == 0 {
        return vec!['0'];
    }
    let mut num = val;
    let mut bits: Vec<char> = Vec::new();
    while num > 0
        invariant num >= 0,
            ValidBitString(bits@),
            Str2Int(bits@) == val % (Exp_int(2, (bits@.len() as nat)))
        decreases num
    {
        if num % 2 == 0 {
            bits.push('0');
        } else {
            bits.push('1');
        }
        num = num / 2;
    }
    bits.reverse();
    return bits;
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
    /* code modified by LLM (iteration 4): Fixed int/nat casting and conversion to bitstring */
    if sy@.len() == 1 {
        let exp_value = if sy@[0] == '0' { 0 } else { 1 };
        let base = Exp_int(Str2Int(sx@), exp_value) % Str2Int(sz@);
        proof {
            nat_to_bitstring_lemma(base);
        }
        return nat_to_bitstring_lemma(base);
    } else {
        let n = sy@.len() - 1;
        let (div, rem) = DivMod(sy, &['0', '1']);
        let pow2_result = ModExpPow2(sx, &div, n as int, sz);
        if Str2Int(rem@) == 1 {
            let temp = (Str2Int(pow2_result@) * Str2Int(sx@)) % Str2Int(sz@);
            proof {
                nat_to_bitstring_lemma(temp);
            }
            return nat_to_bitstring_lemma(temp);
        } else {
            return pow2_result;
        }
    }
}
// </vc-code>

fn main() {}
}
