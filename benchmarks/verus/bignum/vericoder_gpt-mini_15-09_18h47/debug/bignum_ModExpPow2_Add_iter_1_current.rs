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
    let mut i1: int = s1.len() as int - 1;
    let mut i2: int = s2.len() as int - 1;
    let mut carry: int = 0;
    let mut tmp = Vec::<char>::new();
    while i1 >= 0 || i2 >= 0
        invariant
            0 <= i1 + 1,
            0 <= i2 + 1,
        decreases (i1 + 1) + (i2 + 1)
    {
        let b1 = if i1 >= 0 && s1[i1 as usize] == '1' { 1 } else { 0 };
        let b2 = if i2 >= 0 && s2[i2 as usize] == '1' { 1 } else { 0 };
        let sum = b1 + b2 + carry;
        if sum % 2 == 1 {
            tmp.push('1');
        } else {
            tmp.push('0');
        }
        carry = sum / 2;
        i1 -= 1;
        i2 -= 1;
    }
    if carry == 1 {
        tmp.push('1');
    }
    let mut res = Vec::<char>::new();
    let mut j: int = tmp.len() as int - 1;
    while j >= 0
        invariant
            0 <= j + 1,
        decreases j + 1
    {
        res.push(tmp[j as usize]);
        j -= 1;
    }
    res
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
    let mut m: int = 0;
    let mut idx: int = 0;
    while idx < sz.len() as int
        invariant
            0 <= idx,
        decreases sz.len() as int - idx
    {
        let bit = if sz[idx as usize] == '1' { 1 } else { 0 };
        m = 2 * m + bit;
        idx += 1;
    }
    let mut base_mod: int = 0;
    let mut i: int = 0;
    while i < sx.len() as int
        invariant
            0 <= i,
        decreases sx.len() as int - i
    {
        let bit = if sx[i as usize] == '1' { 1 } else { 0 };
        base_mod = (2 * base_mod + bit) % m;
        i += 1;
    }
    let mut is_zero: bool = true;
    let mut k: int = 0;
    while k < sy.len() as int
        invariant
            0 <= k,
        decreases sy.len() as int - k
    {
        if sy[k as usize] == '1' {
            is_zero = false;
            break;
        }
        k += 1;
    }
    let mut result_int: int;
    if is_zero {
        result_int = 1 % m;
    } else {
        let mut r: int = base_mod % m;
        let mut t: int = n;
        while t > 0
            invariant
                0 <= t,
            decreases t
        {
            r = (r * r) % m;
            t -= 1;
        }
        result_int = r % m;
    }
    let mut tmp = Vec::<char>::new();
    if result_int == 0 {
        tmp.push('0');
    } else {
        let mut v = result_int;
        while v > 0
            invariant
                0 <= v,
            decreases v
        {
            let bit = if v % 2 == 1 { '1' } else { '0' };
            tmp.push(bit);
            v = v / 2;
        }
    }
    let mut res = Vec::<char>::new();
    let mut j: int = tmp.len() as int - 1;
    while j >= 0
        invariant
            0 <= j + 1,
        decreases j + 1
    {
        res.push(tmp[j as usize]);
        j -= 1;
    }
    res
}
// </vc-code>

fn main() {}
}


