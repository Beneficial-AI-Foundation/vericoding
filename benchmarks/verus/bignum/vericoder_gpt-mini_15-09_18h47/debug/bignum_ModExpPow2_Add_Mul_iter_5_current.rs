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
    /* code modified by LLM (iteration 5): binary addition using int indices with loop invariants to ensure safe indexing */
    let n1 = s1.len() as int;
    let n2 = s2.len() as int;
    let mut i1: int = n1;
    let mut i2: int = n2;
    let mut carry: int = 0;

    let mut rev = Vec::<char>::new();

    while i1 > 0 || i2 > 0 || carry != 0
        invariant
            0 <= i1 && i1 <= n1,
            0 <= i2 && i2 <= n2,
            carry == 0 || carry == 1,
        decreases i1 + i2 + carry
    {
        let b1 = if i1 == 0 { '0' } else { s1[i1 - 1] };
        let b2 = if i2 == 0 { '0' } else { s2[i2 - 1] };

        let sum = (if b1 == '1' { 1 } else { 0 }) + (if b2 == '1' { 1 } else { 0 }) + carry;
        if sum % 2 == 1 { rev.push('1'); } else { rev.push('0'); }
        carry = if sum >= 2 { 1 } else { 0 };

        if i1 > 0 { i1 -= 1; }
        if i2 > 0 { i2 -= 1; }
    }

    // reverse rev into res
    let mut res = Vec::<char>::new();
    let rlen = rev.len() as int;
    let mut k: int = 0;
    while k < rlen
        invariant
            0 <= k && k <= rlen,
        decreases rlen - k
    {
        res.push(rev[rlen - 1 - k]);
        k += 1;
    }

    res
}

// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): binary multiplication using shift-and-add with int indices and safe accesses */
    // initialize accumulator to "0"
    let mut acc = Vec::<char>::new();
    acc.push('0');

    let n2 = s2.len() as int;
    let mut pos: int = 0; // position from LSB (0 = least significant)
    while pos < n2
        invariant
            0 <= pos && pos <= n2,
        decreases n2 - pos
    {
        // bit at position pos from LSB
        let bit = s2[n2 - 1 - pos];
        if bit == '1' {
            // build shifted copy of s1 (s1 << pos)
            let mut shifted = Vec::<char>::new();

            // copy s1 into shifted
            let n1 = s1.len() as int;
            let mut i: int = 0;
            while i < n1
                invariant
                    0 <= i && i <= n1,
                decreases n1 - i
            {
                shifted.push(s1[i]);
                i += 1;
            }

            // append pos zeros (shift left)
            let mut j: int = 0;
            while j < pos
                invariant
                    0 <= j && j <= pos,
                decreases pos - j
            {
                shifted.push('0');
                j += 1;
            }

            // add shifted into acc using the Add exec function
            acc = Add(acc.as_slice(), shifted.as_slice());
        }
        pos += 1;
    }

    // strip leading zeros except keep single zero if result is zero
    let mut first_one_index: Option<int> = None;
    let mut t: int = 0;
    let alen = acc.len() as int;
    while t < alen
        invariant
            0 <= t && t <= alen,
        decreases alen - t
    {
        if acc[t] == '1' && first_one_index.is_none() { first_one_index = Some(t); }
        t += 1;
    }

    if first_one_index.is_none() {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    // build trimmed result
    let start = first_one_index.unwrap();
    let mut res = Vec::<char>::new();
    let mut p: int = start;
    while p < alen
        invariant
            0 <= p && p <= alen,
        decreases alen - p
    {
        res.push(acc[p]);
        p += 1;
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
    /* code modified by LLM (iteration 5): modular exponentiation for exponent 0 or 2^n using int indices and safe slice access */
    let n_x = sx.len() as int;
    let n_z = sz.len() as int;

    // compute modulo value from sz into modulo (as u128). The requires guarantees modulo > 1 as a mathematical nat
    let mut modulo: u128 = 0;
    let mut iz: int = 0;
    while iz < n_z
        invariant
            0 <= iz && iz <= n_z,
        decreases n_z - iz
    {
        if sz[iz] == '1' { modulo = modulo * 2 + 1; } else { modulo = modulo * 2; }
        iz += 1;
    }

    // safe guard: if modulo is 0 (shouldn't happen given specification), return 0
    if modulo == 0 {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    // compute base mod modulo
    let mut base: u128 = 0;
    let mut ix: int = 0;
    while ix < n_x
        invariant
            0 <= ix && ix <= n_x,
        decreases n_x - ix
    {
        if sx[ix] == '1' { base = (base * 2 + 1) % modulo; } else { base = (base * 2) % modulo; }
        ix += 1;
    }

    // determine if exponent is zero (sy all '0')
    let mut is_zero = true;
    let mut isy: int = 0;
    let n_y = sy.len() as int;
    while isy < n_y
        invariant
            0 <= isy && isy <= n_y,
        decreases n_y - isy
    {
        if sy[isy] == '1' { is_zero = false; }
        isy += 1;
    }

    let mut result_val: u128 = 0;
    if is_zero {
        result_val = 1 % modulo;
    } else {
        // exponent = 2^n with sy.len() == n+1 per requires; perform n squarings
        let n_iter = if n_y == 0 { 0 } else { n_y - 1 };
        let mut cur: u128 = base % modulo;
        let mut i: int = 0;
        while i < n_iter
            invariant
                0 <= i && i <= n_iter,
            decreases n_iter - i
        {
            cur = (cur * cur) % modulo;
            i += 1;
        }
        result_val = cur;
    }

    // convert result_val to binary vector (keep single '0' for zero)
    if result_val == 0 {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    let mut rev = Vec::<char>::new();
    let mut tmp: u128 = result_val;
    while tmp > 0
        invariant
            tmp >= 0,
        decreases tmp
    {
        if tmp % 2 == 1 { rev.push('1'); } else { rev.push('0'); }
        tmp = tmp / 2;
    }

    let mut res = Vec::<char>::new();
    let rlen = rev.len() as int;
    let mut k: int = 0;
    while k < rlen
        invariant
            0 <= k && k <= rlen,
        decreases rlen - k
    {
        res.push(rev[rlen - 1 - k]);
        k += 1;
    }

    res
}

// </vc-code>

fn main() {}
}
