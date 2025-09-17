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
    /* code modified by LLM (iteration 4): per-bit addition without big integers, preserving arbitrary lengths */
    let mut i1: usize = s1.len();
    let mut i2: usize = s2.len();
    let mut carry: u8 = 0u8;
    let mut bits_rev: Vec<char> = Vec::new();
    let max_bits: usize = s1.len() + s2.len() + 1usize;
    while i1 > 0 || i2 > 0 || carry != 0u8
        invariant
            i1 <= s1.len(),
            i2 <= s2.len(),
            bits_rev.len() <= max_bits,
            carry == 0u8 || carry == 1u8,
        decreases
            (i1 + i2 + (carry as usize)) as nat
    {
        let mut b1: u8 = 0u8;
        if i1 > 0 {
            i1 -= 1;
            if s1[i1] == '1' { b1 = 1u8; }
        }
        let mut b2: u8 = 0u8;
        if i2 > 0 {
            i2 -= 1;
            if s2[i2] == '1' { b2 = 1u8; }
        }
        let sum = b1 + b2 + carry;
        let bit = if sum % 2u8 == 1u8 { '1' } else { '0' };
        bits_rev.push(bit);
        carry = if sum >= 2u8 { 1u8 } else { 0u8 };
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
    /* code modified by LLM (iteration 4): modular exponentiation operating on bit-vectors using Add for addition and bitwise algorithms for multiply and reduce */

    // Helper inline: compare two bit-vecs (MSB-first). returns -1 if a<b, 0 if equal, 1 if a>b
    let cmp = |a: &Vec<char>, b: &Vec<char>| -> i8 {
        // find first non-zero index for a
        let mut ia: usize = 0usize;
        while ia < a.len()
            invariant
                ia <= a.len(),
            decreases
                (a.len() - ia) as nat
        {
            if a[ia] != '0' { break; }
            ia += 1;
        }
        let mut ib: usize = 0usize;
        while ib < b.len()
            invariant
                ib <= b.len(),
            decreases
                (b.len() - ib) as nat
        {
            if b[ib] != '0' { break; }
            ib += 1;
        }
        let lena = if ia == a.len() { 1usize } else { a.len() - ia };
        let lenb = if ib == b.len() { 1usize } else { b.len() - ib };
        if lena < lenb { return -1i8; }
        if lena > lenb { return 1i8; }
        // same length, compare digit by digit
        let mut k: usize = 0usize;
        while k < lena
            invariant
                k <= lena,
            decreases
                (lena - k) as nat
        {
            let ca = if ia + k < a.len() { a[ia + k] } else { '0' };
            let cb = if ib + k < b.len() { b[ib + k] } else { '0' };
            if ca < cb { return -1i8; }
            if ca > cb { return 1i8; }
            k += 1;
        }
        0i8
    };

    // Helper inline: subtract b from a, assuming a >= b. returns normalized Vec<char>
    let sub_vec = |a_in: &Vec<char>, b_in: &Vec<char>| -> Vec<char> {
        // perform subtraction from LSB with borrow
        let mut a: Vec<char> = a_in.clone();
        let mut b: Vec<char> = b_in.clone();
        // normalize lengths by prepending zeros to shorter
        if b.len() < a.len() {
            let mut prepend = a.len() - b.len();
            while prepend > 0usize
                invariant
                    prepend <= a.len(),
                decreases
                    prepend as nat
            {
                b.insert(0, '0');
                prepend -= 1;
            }
        } else if a.len() < b.len() {
            let mut prepend = b.len() - a.len();
            while prepend > 0usize
                invariant
                    prepend <= b.len(),
                decreases
                    prepend as nat
            {
                a.insert(0, '0');
                prepend -= 1;
            }
        }
        let mut i: usize = a.len();
        let mut borrow: i8 = 0i8;
        while i > 0usize
            invariant
                i <= a.len(),
            decreases
                i as nat
        {
            i -= 1;
            let ai = if a[i] == '1' { 1i8 } else { 0i8 };
            let bi = if b[i] == '1' { 1i8 } else { 0i8 };
            let mut v = ai - bi - borrow;
            if v < 0 { v += 2; borrow = 1; } else { borrow = 0; }
            a[i] = if v == 1 { '1' } else { '0' };
        }
        // remove leading zeros but keep at least one digit
        while a.len() > 1 && a[0] == '0' {
            a.remove(0);
        }
        a
    };

    // Helper inline: shift left by k (multiply by 2^k): append k '0's at end (LSB-side)
    let shift_left = |v_in: &Vec<char>, k: usize| -> Vec<char> {
        let mut v = v_in.clone();
        let mut kk = k;
        while kk > 0usize
            invariant
                kk <= k,
            decreases
                kk as nat
        {
            v.push('0');
            kk -= 1;
        }
        // normalize: if all zeros, keep single '0'
        if v.len() == 0 { v.push('0'); }
        v
    };

    // Helper inline: multiply a and b using shift-and-add. uses Add for addition.
    let mul_vec = |a_in: &Vec<char>, b_in: &Vec<char>| -> Vec<char> {
        // result initialized to '0'
        let mut res: Vec<char> = Vec::new();
        res.push('0');
        // iterate b from LSB (end) to MSB (start)
        let mut pos: usize = 0usize;
        let mut idx: isize = (b_in.len() as isize) - 1;
        while idx >= 0
            invariant
                idx + 1 >= 0,
            decreases
                (idx + 1) as nat
        {
            let bit = b_in[idx as usize];
            if bit == '1' {
                let partial = shift_left(a_in, pos);
                res = Add(res.as_slice(), partial.as_slice());
            }
            if idx == 0 { break; }
            idx -= 1;
            pos += 1;
        }
        // remove leading zeros
        while res.len() > 1 && res[0] == '0' { res.remove(0); }
        res
    };

    // Helper inline: reduce a modulo m using long-subtract method
    let mod_reduce = |a_in: &Vec<char>, m_in: &Vec<char>| -> Vec<char> {
        let mut a = a_in.clone();
        let mut m = m_in.clone();
        // normalize leading zeros
        while a.len() > 1 && a[0] == '0' { a.remove(0); }
        while m.len() > 1 && m[0] == '0' { m.remove(0); }
        // if a < m return a
        while cmp(&a, &m) >= 0
            invariant
                a.len() >= 1,
            decreases
                a.len() as nat
        {
            let mut shift = if a.len() >= m.len() { a.len() - m.len() } else { 0usize };
            let mut t = shift_left(&m, shift);
            if cmp(&a, &t) < 0 {
                // decrease shift by one
                if shift == 0 { break; }
                shift -= 1;
                t = shift_left(&m, shift);
            }
            a = sub_vec(&a, &t);
            while a.len() > 1 && a[0] == '0' { a.remove(0); }
        }
        a
    };

    // Compute base_mod = Str2Int(sx) % Str2Int(sz) by iterating bits of sx (MSB to LSB)
    let mut base_rem: Vec<char> = Vec::new();
    base_rem.push('0');
    let mut ia: usize = 0usize;
    while ia < sx.len()
        invariant
            ia <= sx.len(),
        decreases
            (sx.len() - ia) as nat
    {
        // rem = (rem * 2) % mod
        let mut t = shift_left(&base_rem, 1usize);
        if cmp(&t, &Vec::from(sz.to_vec())) >= 0 {
            t = sub_vec(&t, &Vec::from(sz.to_vec()));
        }
        if sx[ia] == '1' {
            t = Add(t.as_slice(), &Vec::from(['1']));
            if cmp(&t, &Vec::from(sz.to_vec())) >= 0 {
                t = sub_vec(&t, &Vec::from(sz.to_vec()));
            }
        }
        base_rem = t;
        ia += 1;
    }

    // exponentiate: left-to-right binary exponentiation using bits of sy (MSB to LSB)
    let mut acc: Vec<char> = Vec::new();
    acc.push('1');
    let mut ib: usize = 0usize;
    while ib < sy.len()
        invariant
            ib <= sy.len(),
        decreases
            (sy.len() - ib) as nat
    {
        // acc = (acc * acc) % mod
        let sq = mul_vec(&acc, &acc);
        let sqr = mod_reduce(&sq, &Vec::from(sz.to_vec()));
        acc = sqr;
        if sy[ib] == '1' {
            let mul = mul_vec(&acc, &base_rem);
            let mm = mod_reduce(&mul, &Vec::from(sz.to_vec()));
            acc = mm;
        }
        ib += 1;
    }

    // normalize acc: remove leading zeros but keep one digit
    while acc.len() > 1 && acc[0] == '0' { acc.remove(0); }
    acc
}

// </vc-code>

fn main() {}
}


