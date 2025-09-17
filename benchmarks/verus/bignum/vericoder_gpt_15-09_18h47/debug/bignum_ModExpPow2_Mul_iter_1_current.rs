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
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut n1_u: u128 = 0;
    let mut i1: usize = 0;
    let len1: usize = s1.len();
    while i1 < len1
        invariant
            i1 <= len1,
        decreases (len1 - i1) as int
    {
        let c = s1[i1];
        n1_u = n1_u * 2 + if c == '1' { 1 } else { 0 };
        i1 += 1;
    }
    let mut n2_u: u128 = 0;
    let mut i2: usize = 0;
    let len2: usize = s2.len();
    while i2 < len2
        invariant
            i2 <= len2,
        decreases (len2 - i2) as int
    {
        let c = s2[i2];
        n2_u = n2_u * 2 + if c == '1' { 1 } else { 0 };
        i2 += 1;
    }
    let prod: u128 = n1_u.wrapping_mul(n2_u);
    let mut bits: Vec<char> = Vec::new();
    let mut x: u128 = prod;
    if x == 0 {
        bits.push('0');
    } else {
        while x > 0
            invariant
                true,
            decreases x as int
        {
            let bit = if (x & 1) == 1 { '1' } else { '0' };
            bits.push(bit);
            x = x >> 1;
        }
    }
    let mut res: Vec<char> = Vec::new();
    let mut k: usize = bits.len();
    while k > 0
        invariant
            k <= bits.len(),
            res.len() + k == bits.len(),
        decreases k as int
    {
        k -= 1;
        res.push(bits[k]);
    }
    return res;
}
// </vc-code>

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
    let mut base0: u128 = 0;
    let mut i1: usize = 0;
    let n1: usize = sx.len();
    while i1 < n1
        invariant
            i1 <= n1,
        decreases (n1 - i1) as int
    {
        let c = sx[i1];
        base0 = base0 * 2 + if c == '1' { 1 } else { 0 };
        i1 += 1;
    }
    let mut exp0: u128 = 0;
    let mut i2: usize = 0;
    let n2: usize = sy.len();
    while i2 < n2
        invariant
            i2 <= n2,
        decreases (n2 - i2) as int
    {
        let c = sy[i2];
        exp0 = exp0 * 2 + if c == '1' { 1 } else { 0 };
        i2 += 1;
    }
    let mut modulus: u128 = 0;
    let mut i3: usize = 0;
    let n3: usize = sz.len();
    while i3 < n3
        invariant
            i3 <= n3,
        decreases (n3 - i3) as int
    {
        let c = sz[i3];
        modulus = modulus * 2 + if c == '1' { 1 } else { 0 };
        i3 += 1;
    }
    let m: u128 = if modulus == 0 { 1 } else { modulus };
    let mut base: u128 = base0 % m;
    let mut e: u128 = exp0;
    let mut result_u: u128 = 1 % m;
    while e > 0
        invariant
            m >= 1,
        decreases e as int
    {
        if (e & 1) == 1 {
            result_u = (result_u.wrapping_mul(base)) % m;
        }
        base = (base.wrapping_mul(base)) % m;
        e = e >> 1;
    }
    let value: u128 = result_u % m;
    let mut bits: Vec<char> = Vec::new();
    let mut x: u128 = value;
    if x == 0 {
        bits.push('0');
    } else {
        while x > 0
            invariant
                true,
            decreases x as int
        {
            let bit = if (x & 1) == 1 { '1' } else { '0' };
            bits.push(bit);
            x = x >> 1;
        }
    }
    let mut res: Vec<char> = Vec::new();
    let mut k: usize = bits.len();
    while k > 0
        invariant
            k <= bits.len(),
            res.len() + k == bits.len(),
        decreases k as int
    {
        k -= 1;
        res.push(bits[k]);
    }
    return res;
}
// </vc-code>

fn main() {}
}


