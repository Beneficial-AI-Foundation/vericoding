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

// <vc-helpers>
/* helper modified by LLM (iteration 8): big-integer bitvector operations (Vec<char> with MSB at index 0, LSB at end) for modular arithmetic */
fn trim_leading(mut v: Vec<char>) -> Vec<char> {
    // remove leading '0's; keep empty for zero
    while v.len() > 0 && v[0] == '0' {
        v.remove(0);
    }
    v
}

fn cmp_vec(a: &Vec<char>, b: &Vec<char>) -> i8 {
    let a_t = trim_leading(a.clone());
    let b_t = trim_leading(b.clone());
    if a_t.len() > b_t.len() { return 1; }
    if a_t.len() < b_t.len() { return -1; }
    let mut i: usize = 0usize;
    while i < a_t.len() {
        if a_t[i] > b_t[i] { return 1; }
        if a_t[i] < b_t[i] { return -1; }
        i += 1usize;
    }
    0
}

fn add_vec(a: Vec<char>, b: Vec<char>) -> Vec<char> {
    // add bitvectors a and b (MSB..LSB) -> result trimmed
    let mut res_rev: Vec<char> = Vec::new();
    let mut carry: u8 = 0u8;
    let mut ia: isize = a.len() as isize - 1;
    let mut ib: isize = b.len() as isize - 1;
    while ia >= 0 || ib >= 0 || carry > 0 {
        let abit: u8 = if ia >= 0 { if a[ia as usize] == '1' { 1 } else { 0 } } else { 0 };
        let bbit: u8 = if ib >= 0 { if b[ib as usize] == '1' { 1 } else { 0 } } else { 0 };
        let sum = abit + bbit + carry;
        res_rev.push(if (sum % 2) == 1 { '1' } else { '0' });
        carry = if sum >= 2 { 1 } else { 0 };
        ia -= 1;
        ib -= 1;
    }
    // reverse
    let mut res: Vec<char> = Vec::new();
    let mut j: usize = 0usize;
    while j < res_rev.len() {
        res.push(res_rev[res_rev.len() - 1 - j]);
        j += 1usize;
    }
    trim_leading(res)
}

fn sub_vec(a: Vec<char>, b: Vec<char>) -> Vec<char> {
    // assumes a >= b, compute a - b
    let mut res_rev: Vec<char> = Vec::new();
    let mut borrow: i8 = 0;
    let mut ia: isize = a.len() as isize - 1;
    let mut ib: isize = b.len() as isize - 1;
    while ia >= 0 || ib >= 0 {
        let abit: i8 = if ia >= 0 { if a[ia as usize] == '1' { 1 } else { 0 } } else { 0 };
        let bbit: i8 = if ib >= 0 { if b[ib as usize] == '1' { 1 } else { 0 } } else { 0 };
        let mut v = abit - bbit - borrow;
        if v >= 0 {
            res_rev.push(if v == 1 { '1' } else { '0' });
            borrow = 0;
        } else {
            // borrow from next higher bit
            v += 2;
            res_rev.push(if v == 1 { '1' } else { '0' });
            borrow = 1;
        }
        ia -= 1;
        ib -= 1;
    }
    // remove trailing zeros in reversed representation
    let mut res: Vec<char> = Vec::new();
    let mut j: usize = 0usize;
    while j < res_rev.len() {
        res.push(res_rev[res_rev.len() - 1 - j]);
        j += 1usize;
    }
    trim_leading(res)
}

fn shift_left(a: Vec<char>, k: usize) -> Vec<char> {
    if a.len() == 0 { return Vec::new(); }
    let mut r = a.clone();
    let mut i: usize = 0usize;
    while i < k {
        r.push('0');
        i += 1usize;
    }
    r
}

fn mul_vec(a: Vec<char>, b: Vec<char>) -> Vec<char> {
    // schoolbook: for each 1-bit in b add shifted a
    if a.len() == 0 || b.len() == 0 { return Vec::new(); }
    let mut res: Vec<char> = Vec::new(); // zero
    let mut pos: usize = 0usize;
    let mut ib: isize = b.len() as isize - 1;
    while ib >= 0 {
        if b[ib as usize] == '1' {
            let term = shift_left(a.clone(), pos);
            res = add_vec(res, term);
        }
        pos += 1usize;
        ib -= 1;
    }
    trim_leading(res)
}

fn mod_reduce(mut v: Vec<char>, m: &Vec<char>) -> Vec<char> {
    // reduce v modulo m by repeated subtraction
    let mut cmp = cmp_vec(&v, m);
    while cmp >= 0 {
        v = sub_vec(v, m.clone());
        cmp = cmp_vec(&v, m);
    }
    v
}

fn mul_mod(a: Vec<char>, b: Vec<char>, m: &Vec<char>) -> Vec<char> {
    if m.len() == 0 { return Vec::new(); }
    let prod = mul_vec(a, b);
    if prod.len() == 0 { return Vec::new(); }
    mod_reduce(prod, m)
}

fn pow_mod(base_in: Vec<char>, exp: Vec<char>, m: Vec<char>) -> Vec<char> {
    // exponentiation by squaring using bits from LSB (end) to MSB (start)
    let mut base = mod_reduce(base_in, &m);
    let mut result: Vec<char> = Vec::new();
    // represent 1 as ['1']
    result.push('1');
    // if m == 0-length, treat oddly, but preconditions ensure modulus > 1 in spec
    let mut iex: isize = exp.len() as isize - 1;
    while iex >= 0 {
        // exp bit at position (from MSB..LSB): exp[iex]
        // but we need LSB-first processing: LSB is at end, so iterating from end to start gives LSB->MSB
        if exp[iex as usize] == '1' {
            result = mul_mod(result, base.clone(), &m);
        }
        base = mul_mod(base.clone(), base.clone(), &m);
        iex -= 1;
    }
    // trim result
    trim_leading(result)
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 8): runtime modular exponentiation over bit-vector Vec<char> using helpers */
    // convert input slices to Vec<char>
    let mut vx: Vec<char> = Vec::new();
    let mut i: usize = 0usize;
    while i < sx.len() {
        vx.push(sx[i]);
        i += 1usize;
    }
    let mut vy: Vec<char> = Vec::new();
    i = 0usize;
    while i < sy.len() {
        vy.push(sy[i]);
        i += 1usize;
    }
    let mut vz: Vec<char> = Vec::new();
    i = 0usize;
    while i < sz.len() {
        vz.push(sz[i]);
        i += 1usize;
    }

    let res = pow_mod(vx, vy, vz);
    res
}

// </vc-code>

fn main() {}
}
