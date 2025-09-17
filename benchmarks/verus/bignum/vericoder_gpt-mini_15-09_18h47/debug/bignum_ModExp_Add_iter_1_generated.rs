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

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut v1: u128 = 0u128;
    let mut i: usize = 0usize;
    while i < s1.len() {
        v1 = v1 * 2u128 + if s1[i] == '1' { 1u128 } else { 0u128 };
        i += 1;
    }

    let mut v2: u128 = 0u128;
    i = 0usize;
    while i < s2.len() {
        v2 = v2 * 2u128 + if s2[i] == '1' { 1u128 } else { 0u128 };
        i += 1;
    }

    let mut sum = v1 + v2;

    let mut bits_rev: Vec<char> = Vec::new();
    if sum == 0u128 {
        bits_rev.push('0');
    } else {
        while sum > 0u128 {
            let b = if sum % 2u128 == 1u128 { '1' } else { '0' };
            bits_rev.push(b);
            sum = sum / 2u128;
        }
    }

    let mut res: Vec<char> = Vec::new();
    let mut j: usize = bits_rev.len();
    while j > 0usize {
        j -= 1;
        res.push(bits_rev[j]);
    }

    res
}
// </vc-code>

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
    let mut base: u128 = 0u128;
    let mut i: usize = 0usize;
    while i < sx.len() {
        base = base * 2u128 + if sx[i] == '1' { 1u128 } else { 0u128 };
        i += 1;
    }

    let mut exp: u128 = 0u128;
    i = 0usize;
    while i < sy.len() {
        exp = exp * 2u128 + if sy[i] == '1' { 1u128 } else { 0u128 };
        i += 1;
    }

    let mut modu: u128 = 0u128;
    i = 0usize;
    while i < sz.len() {
        modu = modu * 2u128 + if sz[i] == '1' { 1u128 } else { 0u128 };
        i += 1;
    }

    // modular exponentiation (binary exp)
    let mut base_mod = if modu == 0u128 { 0u128 } else { base % modu };
    let mut e = exp;
    let mut acc: u128 = if modu == 0u128 { base_mod } else { 1u128 % modu };

    while e > 0u128 {
        if e % 2u128 == 1u128 {
            if modu == 0u128 { acc = acc * base_mod; } else { acc = (acc * base_mod) % modu; }
        }
        e = e / 2u128;
        if modu == 0u128 { base_mod = base_mod * base_mod; } else { base_mod = (base_mod * base_mod) % modu; }
    }

    // convert acc to binary big-endian Vec<char>
    let mut val = acc;
    let mut bits_rev: Vec<char> = Vec::new();
    if val == 0u128 {
        bits_rev.push('0');
    } else {
        while val > 0u128 {
            let b = if val % 2u128 == 1u128 { '1' } else { '0' };
            bits_rev.push(b);
            val = val / 2u128;
        }
    }
    let mut res: Vec<char> = Vec::new();
    let mut j: usize = bits_rev.len();
    while j > 0usize {
        j -= 1;
        res.push(bits_rev[j]);
    }

    res
}
// </vc-code>

fn main() {}
}


