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
    /* code modified by LLM (iteration 3): binary multiplication via shifts and adds */
    let mut res = Vec::<char>::new();
    res.push('0');

    let mut i: usize = 0;
    while i < s2.len()
        invariant
            i <= s2.len(),
        decreases s2.len() - i
    {
        let bit = s2[s2.len() - 1 - i];
        if bit == '1' {
            // build temp = s1 shifted left by i (append i zeros at end)
            let mut temp = Vec::<char>::new();
            let mut j: usize = 0;
            while j < s1.len()
                invariant
                    j <= s1.len(),
                decreases s1.len() - j
            {
                temp.push(s1[j]);
                j += 1;
            }
            let mut k: usize = 0;
            while k < i
                invariant
                    k <= i,
                decreases i - k
            {
                temp.push('0');
                k += 1;
            }

            // add res and temp (binary addition)
            let mut sum = Vec::<char>::new();
            let mut carry = false;
            let mut pos: usize = 0;
            let max_len = if res.len() > temp.len() { res.len() } else { temp.len() };
            while pos < max_len
                invariant
                    pos <= max_len,
                decreases max_len - pos
            {
                let ai = if pos < res.len() { res[res.len() - 1 - pos] } else { '0' };
                let bi = if pos < temp.len() { temp[temp.len() - 1 - pos] } else { '0' };
                let mut s_int: u8 = 0;
                if ai == '1' { s_int += 1; }
                if bi == '1' { s_int += 1; }
                if carry { s_int += 1; }
                let digit = if s_int % 2 == 1 { '1' } else { '0' };
                carry = s_int >= 2;
                sum.insert(0, digit);
                pos += 1;
            }
            if carry {
                sum.insert(0, '1');
            }
            while sum.len() > 1 && sum[0] == '0'
                invariant
                    sum.len() >= 1,
                decreases sum.len()
            {
                sum.remove(0);
            }
            res = sum;
        }
        i += 1;
    }

    if res.len() == 0 {
        res.push('0');
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
    /* code modified by LLM (iteration 3): modular exponentiation for power-of-two exponent without saturating_sub */
    // parse base
    let mut base: u128 = 0u128;
    let mut idx: usize = 0;
    while idx < sx.len()
        invariant
            idx <= sx.len(),
        decreases sx.len() - idx
    {
        base = base * 2u128 + if sx[idx] == '1' { 1u128 } else { 0u128 };
        idx += 1;
    }

    // parse modu
    let mut modu: u128 = 0u128;
    idx = 0;
    while idx < sz.len()
        invariant
            idx <= sz.len(),
        decreases sz.len() - idx
    {
        modu = modu * 2u128 + if sz[idx] == '1' { 1u128 } else { 0u128 };
        idx += 1;
    }

    // handle modulo 0 edge case defensively (spec ensures >1)
    if modu == 0u128 {
        let mut res = Vec::<char>::new();
        res.push('0');
        return res;
    }

    // compute n safely without saturating_sub
    let n_usize: usize = if sy.len() >= 1 { sy.len() - 1 } else { 0 };

    // detect if sy is zero
    let mut is_zero = true;
    idx = 0;
    while idx < sy.len()
        invariant
            idx <= sy.len(),
        decreases sy.len() - idx
    {
        if sy[idx] == '1' { is_zero = false; }
        idx += 1;
    }

    // compute result: if exponent is zero => 1 % modu, else compute repeated squaring n times
    let mut result_int: u128 = 1u128 % modu;
    if !is_zero {
        result_int = base % modu;
        let mut c: usize = 0;
        while c < n_usize
            invariant
                c <= n_usize,
            decreases n_usize - c
        {
            result_int = (result_int * result_int) % modu;
            c += 1;
        }
    }

    // convert result_int to bit vector (MSB..LSB)
    let mut res = Vec::<char>::new();
    if result_int == 0u128 {
        res.push('0');
        return res;
    }

    let mut bits_rev = Vec::<char>::new();
    let mut v: u128 = result_int;
    while v > 0u128
        invariant
            v >= 0u128,
        decreases v
    {
        let bit = if v % 2u128 == 1u128 { '1' } else { '0' };
        bits_rev.push(bit);
        v = v / 2u128;
    }

    let mut p: usize = 0;
    while p < bits_rev.len()
        invariant
            p <= bits_rev.len(),
        decreases bits_rev.len() - p
    {
        res.insert(0, bits_rev[p]);
        p += 1;
    }

    res
}

// </vc-code>

fn main() {}
}


