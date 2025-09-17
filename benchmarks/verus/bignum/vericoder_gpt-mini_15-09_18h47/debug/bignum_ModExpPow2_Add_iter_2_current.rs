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
    /* code modified by LLM (iteration 2): use usize indices and perform binary addition with carry */
    let mut i1: usize = s1.len();
    let mut i2: usize = s2.len();
    let mut carry: u8 = 0;
    let mut tmp = Vec::<char>::new();
    while i1 > 0 || i2 > 0
        invariant
            i1 <= s1.len(),
            i2 <= s2.len(),
        decreases i1 + i2
    {
        let b1: u8 = if i1 > 0 { i1 -= 1; if s1[i1] == '1' { 1 } else { 0 } } else { 0 };
        let b2: u8 = if i2 > 0 { i2 -= 1; if s2[i2] == '1' { 1 } else { 0 } } else { 0 };
        let sum = b1 + b2 + carry;
        if sum % 2 == 1 {
            tmp.push('1');
        } else {
            tmp.push('0');
        }
        carry = sum / 2;
    }
    if carry == 1 {
        tmp.push('1');
    }
    let mut res = Vec::<char>::new();
    let mut j: usize = tmp.len();
    while j > 0
        invariant
            j <= tmp.len(),
        decreases j
    {
        j -= 1;
        res.push(tmp[j]);
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
    /* code modified by LLM (iteration 2): parse modulus, compute base mod and exponentiate by repeated squaring using usize */
    let mut m: usize = 0;
    let mut idx: usize = 0;
    while idx < sz.len()
        invariant
            idx <= sz.len(),
        decreases sz.len() - idx
    {
        let bit = if sz[idx] == '1' { 1usize } else { 0usize };
        m = 2 * m + bit;
        idx += 1;
    }
    // m > 1 is guaranteed by requires
    let mut base_mod: usize = 0;
    let mut i: usize = 0;
    while i < sx.len()
        invariant
            i <= sx.len(),
        decreases sx.len() - i
    {
        let bit = if sx[i] == '1' { 1usize } else { 0usize };
        base_mod = (2 * base_mod + bit) % m;
        i += 1;
    }
    // check if sy represents zero
    let mut is_zero: bool = true;
    let mut k: usize = 0;
    while k < sy.len()
        invariant
            k <= sy.len(),
        decreases sy.len() - k
    {
        if sy[k] == '1' {
            is_zero = false;
            break;
        }
        k += 1;
    }
    let mut result_int: usize;
    if is_zero {
        result_int = 1 % m;
    } else {
        let mut r: usize = base_mod % m;
        // n equals sy.len() - 1 per requires
        let mut t: usize = if sy.len() == 0 { 0 } else { sy.len() - 1 };
        while t > 0
            invariant
                t <= (sy.len() - 1),
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
        let mut v: usize = result_int;
        while v > 0
            invariant
                v >= 0,
            decreases v
        {
            let bit = if v % 2 == 1 { '1' } else { '0' };
            tmp.push(bit);
            v = v / 2;
        }
    }
    let mut res = Vec::<char>::new();
    let mut j: usize = tmp.len();
    while j > 0
        invariant
            j <= tmp.len(),
        decreases j
    {
        j -= 1;
        res.push(tmp[j]);
    }
    res
}
// </vc-code>

fn main() {}
}


