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
/* helper modified by LLM (iteration 9): added loop invariants and decreases to ensure termination */
fn trim_leading(mut v: Vec<char>) -> Vec<char> {
    let orig = v.len();
    while v.len() > 0 && v[0] == '0'
        invariant
            v.len() <= orig,
        decreases orig - v.len()
    {
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
    while i < a_t.len()
        invariant
            i <= a_t.len(),
        decreases a_t.len() - i
    {
        if a_t[i] > b_t[i] { return 1; }
        if a_t[i] < b_t[i] { return -1; }
        i += 1usize;
    }
    0
}

fn add_vec(a: Vec<char>, b: Vec<char>) -> Vec<char> {
    let na = a.len();
    let nb = b.len();
    let max_len = if na > nb { na } else { nb };
    let mut res_rev: Vec<char> = Vec::new();
    let mut carry: u8 = 0u8;
    let mut k: usize = 0usize;
    while k < max_len
        invariant
            k <= max_len,
        decreases max_len - k
    {
        let abit: u8 = if k < na { if a[na - 1 - k] == '1' { 1 } else { 0 } } else { 0 };
        let bbit: u8 = if k < nb { if b[nb - 1 - k] == '1' { 1 } else { 0 } } else { 0 };
        let sum = abit + bbit + carry;
        res_rev.push(if (sum % 2) == 1 { '1' } else { '0' });
        carry = if sum >= 2 { 1 } else { 0 };
        k += 1usize;
    }
    if carry > 0 {
        res_rev.push('1');
    }
    let mut res: Vec<char> = Vec::new();
    let mut j: usize = 0usize;
    while j < res_rev.len()
        invariant
            j <= res_rev.len(),
        decreases res_rev.len() - j
    {
        res.push(res_rev[res_rev.len() - 1 - j]);
        j += 1usize;
    }
    trim_leading(res)
}

fn sub_vec(a: Vec<char>, b: Vec<char>) -> Vec<char> {
    let na = a.len();
    let nb = b.len();
    let max_len = if na > nb { na } else { nb };
    let mut res_rev: Vec<char> = Vec::new();
    let mut borrow: i8 = 0;
    let mut k: usize = 0usize;
    while k < max_len
        invariant
            k <= max_len,
        decreases max_len - k
    {
        let abit: i8 = if k < na { if a[na - 1 - k] == '1' { 1 } else { 0 } } else { 0 };
        let bbit: i8 = if k < nb { if b[nb - 1 - k] == '1' { 1 } else { 0 } } else { 0 };
        let mut v = abit - bbit - borrow;
        if v >= 0 {
            res_rev.push(if v == 1 { '1' } else { '0' });
            borrow = 0;
        } else {
            v += 2;
            res_rev.push(if v == 1 { '1' } else { '0' });
            borrow = 1;
        }
        k += 1usize;
    }
    let mut res: Vec<char> = Vec::new();
    let mut j: usize = 0usize;
    while j < res_rev.len()
        invariant
            j <= res_rev.len(),
        decreases res_rev.len() - j
    {
        res.push(res_rev[res_rev.len() - 1 - j]);
        j += 1usize;
    }
    trim_leading(res)
}

fn shift_left(a: Vec<char>, k: usize) -> Vec<char> {
    if a.len() == 0 { return Vec::new(); }
    let mut r = a.clone();
    let mut i: usize = 0usize;
    while i < k
        invariant
            i <= k,
        decreases k - i
    {
        r.push('0');
        i += 1usize;
    }
    r
}

fn mul_vec(a: Vec<char>, b: Vec<char>) -> Vec<char> {
    if a.len() == 0 || b.len() == 0 { return Vec::new(); }
    let mut res: Vec<char> = Vec::new();
    let nb = b.len();
    let mut pos: usize = 0usize;
    while pos < nb
        invariant
            pos <= nb,
        decreases nb - pos
    {
        if b[nb - 1 - pos] == '1' {
            let term = shift_left(a.clone(), pos);
            res = add_vec(res, term);
        }
        pos += 1usize;
    }
    trim_leading(res)
}

fn mod_reduce(mut v: Vec<char>, m: &Vec<char>) -> Vec<char> {
    while cmp_vec(&v, m) >= 0
        invariant
            Str2Int(v@) >= 0,
        decreases Str2Int(v@)
    {
        v = sub_vec(v, m.clone());
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
    let mut base = mod_reduce(base_in, &m);
    let mut result: Vec<char> = Vec::new();
    result.push('1');
    let nb = exp.len();
    let mut pos: usize = 0usize;
    while pos < nb
        invariant
            pos <= nb,
        decreases nb - pos
    {
        if exp[nb - 1 - pos] == '1' {
            result = mul_mod(result, base.clone(), &m);
        }
        base = mul_mod(base.clone(), base.clone(), &m);
        pos += 1usize;
    }
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
    /* code modified by LLM (iteration 9): copy input slices to Vec<char> with loop invariants/decreases, then compute pow_mod */
    let mut vx: Vec<char> = Vec::new();
    let mut i: usize = 0usize;
    while i < sx.len()
        invariant
            i <= sx.len(),
        decreases sx.len() - i
    {
        vx.push(sx[i]);
        i += 1usize;
    }
    let mut vy: Vec<char> = Vec::new();
    i = 0usize;
    while i < sy.len()
        invariant
            i <= sy.len(),
        decreases sy.len() - i
    {
        vy.push(sy[i]);
        i += 1usize;
    }
    let mut vz: Vec<char> = Vec::new();
    i = 0usize;
    while i < sz.len()
        invariant
            i <= sz.len(),
        decreases sz.len() - i
    {
        vz.push(sz[i]);
        i += 1usize;
    }

    let res = pow_mod(vx, vy, vz);
    res
}

// </vc-code>

fn main() {}
}
