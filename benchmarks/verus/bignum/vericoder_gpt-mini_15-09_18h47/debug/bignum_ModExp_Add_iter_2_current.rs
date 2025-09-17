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
    /* code modified by LLM (iteration 2): added loop invariants and decreases; bounded bit loops */
    let mut v1: u128 = 0u128;
    let mut i: usize = 0usize;
    while i < s1.len()
        invariant
            i <= s1.len(),
        decreases
            (s1.len() - i) as nat
    {
        v1 = v1 * 2u128 + if s1[i] == '1' { 1u128 } else { 0u128 };
        i += 1;
    }

    let mut v2: u128 = 0u128;
    i = 0usize;
    while i < s2.len()
        invariant
            i <= s2.len(),
        decreases
            (s2.len() - i) as nat
    {
        v2 = v2 * 2u128 + if s2[i] == '1' { 1u128 } else { 0u128 };
        i += 1;
    }

    let mut sum = v1 + v2;

    const MAX_BITS: usize = 128usize;
    let mut bits_rev: Vec<char> = Vec::new();
    if sum == 0u128 {
        bits_rev.push('0');
    } else {
        while sum > 0u128
            invariant
                bits_rev.len() <= MAX_BITS,
            decreases
                (MAX_BITS - bits_rev.len()) as nat
        {
            let b = if sum % 2u128 == 1u128 { '1' } else { '0' };
            bits_rev.push(b);
            sum = sum / 2u128;
        }
    }

    let mut res: Vec<char> = Vec::new();
    let mut j: usize = bits_rev.len();
    while j > 0usize
        invariant
            j <= bits_rev.len(),
        decreases
            j as nat
    {
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
    /* code modified by LLM (iteration 2): added loop invariants/decreases and bitwise exponent loop */
    let mut base: u128 = 0u128;
    let mut i: usize = 0usize;
    while i < sx.len()
        invariant
            i <= sx.len(),
        decreases
            (sx.len() - i) as nat
    {
        base = base * 2u128 + if sx[i] == '1' { 1u128 } else { 0u128 };
        i += 1;
    }

    let mut exp: u128 = 0u128;
    i = 0usize;
    while i < sy.len()
        invariant
            i <= sy.len(),
        decreases
            (sy.len() - i) as nat
    {
        exp = exp * 2u128 + if sy[i] == '1' { 1u128 } else { 0u128 };
        i += 1;
    }

    let mut modu: u128 = 0u128;
    i = 0usize;
    while i < sz.len()
        invariant
            i <= sz.len(),
        decreases
            (sz.len() - i) as nat
    {
        modu = modu * 2u128 + if sz[i] == '1' { 1u128 } else { 0u128 };
        i += 1;
    }

    const MAX_BITS: usize = 128usize;
    let mut base_mod = base % modu;
    let mut acc: u128 = 1u128 % modu;

    // build exponent bits (LSB first)
    let mut exp_tmp = exp;
    let mut exp_bits_rev: Vec<char> = Vec::new();
    if exp_tmp == 0u128 {
        exp_bits_rev.push('0');
    } else {
        while exp_tmp > 0u128
            invariant
                exp_bits_rev.len() <= MAX_BITS,
            decreases
                (MAX_BITS - exp_bits_rev.len()) as nat
        {
            let b = if exp_tmp % 2u128 == 1u128 { '1' } else { '0' };
            exp_bits_rev.push(b);
            exp_tmp = exp_tmp / 2u128;
        }
    }

    // iterate over exponent bits (LSB to MSB)
    let mut k: usize = 0usize;
    while k < exp_bits_rev.len()
        invariant
            k <= exp_bits_rev.len(),
        decreases
            (exp_bits_rev.len() - k) as nat
    {
        if exp_bits_rev[k] == '1' {
            acc = (acc * base_mod) % modu;
        }
        base_mod = (base_mod * base_mod) % modu;
        k += 1;
    }

    // convert acc to binary big-endian Vec<char>
    let mut val = acc;
    let mut bits_rev: Vec<char> = Vec::new();
    if val == 0u128 {
        bits_rev.push('0');
    } else {
        while val > 0u128
            invariant
                bits_rev.len() <= MAX_BITS,
            decreases
                (MAX_BITS - bits_rev.len()) as nat
        {
            let b = if val % 2u128 == 1u128 { '1' } else { '0' };
            bits_rev.push(b);
            val = val / 2u128;
        }
    }
    let mut res: Vec<char> = Vec::new();
    let mut j: usize = bits_rev.len();
    while j > 0usize
        invariant
            j <= bits_rev.len(),
        decreases
            j as nat
    {
        j -= 1;
        res.push(bits_rev[j]);
    }

    res
}
// </vc-code>

fn main() {}
}


