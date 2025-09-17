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
    /* code modified by LLM (iteration 6): binary addition using usize indices and safe accesses */
    let n1: usize = s1.len();
    let n2: usize = s2.len();
    let mut i1: usize = n1;
    let mut i2: usize = n2;
    let mut carry: usize = 0;

    let mut rev = Vec::<char>::new();

    while i1 > 0 || i2 > 0 || carry != 0
        invariant
            0usize <= i1 && i1 <= n1,
            0usize <= i2 && i2 <= n2,
            carry == 0usize || carry == 1usize,
        decreases i1 + i2 + carry
    {
        let b1 = if i1 == 0 { '0' } else { s1[i1 - 1] };
        let b2 = if i2 == 0 { '0' } else { s2[i2 - 1] };
        let v1 = if b1 == '1' { 1usize } else { 0usize };
        let v2 = if b2 == '1' { 1usize } else { 0usize };
        let sum = v1 + v2 + carry;
        if sum % 2 == 1 { rev.push('1'); } else { rev.push('0'); }
        carry = if sum >= 2 { 1usize } else { 0usize };
        if i1 > 0 { i1 -= 1; }
        if i2 > 0 { i2 -= 1; }
    }

    let mut res = Vec::<char>::new();
    let rlen: usize = rev.len();
    let mut k: usize = 0;
    while k < rlen
        invariant
            0usize <= k && k <= rlen,
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
    /* code modified by LLM (iteration 6): binary multiplication using shift-and-add with usize indices and safe accesses */
    let mut acc = Vec::<char>::new();
    acc.push('0');

    let n2: usize = s2.len();
    let mut pos: usize = 0;
    while pos < n2
        invariant
            0usize <= pos && pos <= n2,
        decreases n2 - pos
    {
        let bit = s2[n2 - 1 - pos];
        if bit == '1' {
            let mut shifted = Vec::<char>::new();

            let n1: usize = s1.len();
            let mut i: usize = 0;
            while i < n1
                invariant
                    0usize <= i && i <= n1,
                decreases n1 - i
            {
                shifted.push(s1[i]);
                i += 1;
            }

            let mut j: usize = 0;
            while j < pos
                invariant
                    0usize <= j && j <= pos,
                decreases pos - j
            {
                shifted.push('0');
                j += 1;
            }

            acc = Add(acc.as_slice(), shifted.as_slice());
        }
        pos += 1;
    }

    let mut first_one_index: Option<usize> = None;
    let mut t: usize = 0;
    let alen: usize = acc.len();
    while t < alen
        invariant
            0usize <= t && t <= alen,
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

    let start = first_one_index.unwrap();
    let mut res = Vec::<char>::new();
    let mut p: usize = start;
    while p < alen
        invariant
            0usize <= p && p <= alen,
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
    /* code modified by LLM (iteration 6): modular exponentiation for exponent 0 or 2^n using usize indices and u128 arithmetic */
    let n_x: usize = sx.len();
    let n_z: usize = sz.len();

    let mut modulo: u128 = 0;
    let mut iz: usize = 0;
    while iz < n_z
        invariant
            0usize <= iz && iz <= n_z,
        decreases n_z - iz
    {
        modulo = modulo * 2 + if sz[iz] == '1' { 1 } else { 0 };
        iz += 1;
    }

    if modulo == 0 {
        let mut zero = Vec::<char>::new();
        zero.push('0');
        return zero;
    }

    let mut base: u128 = 0;
    let mut ix: usize = 0;
    while ix < n_x
        invariant
            0usize <= ix && ix <= n_x,
        decreases n_x - ix
    {
        base = (base * 2 + if sx[ix] == '1' { 1 } else { 0 }) % modulo;
        ix += 1;
    }

    let mut is_zero: bool = true;
    let n_y: usize = sy.len();
    let mut isy: usize = 0;
    while isy < n_y
        invariant
            0usize <= isy && isy <= n_y,
        decreases n_y - isy
    {
        if sy[isy] == '1' { is_zero = false; }
        isy += 1;
    }

    let mut result_val: u128 = 0;
    if is_zero {
        result_val = 1 % modulo;
    } else {
        let n_iter: usize = if n_y == 0 { 0 } else { n_y - 1 };
        let mut cur: u128 = base % modulo;
        let mut i: usize = 0;
        while i < n_iter
            invariant
                0usize <= i && i <= n_iter,
            decreases n_iter - i
        {
            cur = (cur * cur) % modulo;
            i += 1;
        }
        result_val = cur;
    }

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
    let rlen: usize = rev.len();
    let mut k: usize = 0;
    while k < rlen
        invariant
            0usize <= k && k <= rlen,
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
