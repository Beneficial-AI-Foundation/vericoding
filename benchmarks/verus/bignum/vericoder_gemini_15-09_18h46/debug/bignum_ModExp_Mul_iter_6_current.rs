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
    /* code modified by LLM (iteration 6): Added 'nat' suffix to integer literals to fix compilation type errors. */
    let mut n1: nat = 0nat;
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            ValidBitString(s1@),
            0 <= i <= s1.len(),
            n1 == Str2Int(s1@.subrange(0, i as int)),
        decreases s1.len() - i
    {
        n1 = n1 * 2nat + (if s1[i] == '1' { 1nat } else { 0nat });
        i = i + 1;
    }

    let mut n2: nat = 0nat;
    i = 0;
    while i < s2.len()
        invariant
            ValidBitString(s2@),
            0 <= i <= s2.len(),
            n2 == Str2Int(s2@.subrange(0, i as int)),
        decreases s2.len() - i
    {
        n2 = n2 * 2nat + (if s2[i] == '1' { 1nat } else { 0nat });
        i = i + 1;
    }

    let res_n = n1 * n2;

    if res_n == 0nat {
        let mut res = Vec::new();
        res.push('0');
        return res;
    }

    let mut temp_n = res_n;
    let mut rev_res = Vec::new();
    while temp_n > 0nat
        invariant
            res_n > 0nat,
            ValidBitString(rev_res@),
            res_n == temp_n * Exp_int(2nat, rev_res@.len() as nat) + Str2Int(rev_res@.reverse()),
        decreases temp_n
    {
        if temp_n % 2nat == 1nat {
            rev_res.push('1');
        } else {
            rev_res.push('0');
        }
        temp_n = temp_n / 2nat;
    }

    let mut res = Vec::new();
    let mut k: usize = 0;
    let rev_len = rev_res.len();
    while k < rev_len
        invariant
            rev_len == rev_res.len(),
            0 <= k <= rev_len,
            ValidBitString(res@),
            res@ == rev_res@.subrange(0, k as int).reverse(),
        decreases rev_len - k
    {
        res.push(rev_res[rev_len - 1 - k]);
        k = k + 1;
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
    /* code modified by LLM (iteration 6): Added 'nat' suffix to integer literals to fix compilation type errors. */
    let mut sx_n: nat = 0nat;
    let mut i: usize = 0;
    while i < sx.len()
        invariant
            ValidBitString(sx@),
            0 <= i <= sx.len(),
            sx_n == Str2Int(sx@.subrange(0, i as int)),
        decreases sx.len() - i
    {
        sx_n = sx_n * 2nat + (if sx[i] == '1' { 1nat } else { 0nat });
        i = i + 1;
    }

    let mut sy_n: nat = 0nat;
    i = 0;
    while i < sy.len()
        invariant
            ValidBitString(sy@),
            0 <= i <= sy.len(),
            sy_n == Str2Int(sy@.subrange(0, i as int)),
        decreases sy.len() - i
    {
        sy_n = sy_n * 2nat + (if sy[i] == '1' { 1nat } else { 0nat });
        i = i + 1;
    }

    let mut sz_n: nat = 0nat;
    i = 0;
    while i < sz.len()
        invariant
            ValidBitString(sz@),
            0 <= i <= sz.len(),
            sz_n == Str2Int(sz@.subrange(0, i as int)),
        decreases sz.len() - i
    {
        sz_n = sz_n * 2nat + (if sz[i] == '1' { 1nat } else { 0nat });
        i = i + 1;
    }

    let x = sx_n;
    let y = sy_n;
    let z = sz_n;

    let mut res_n: nat = 1nat;
    let mut base = x % z;
    let mut exp = y;
    while exp > 0nat
        invariant
            z > 1nat,
            Exp_int(x, y) % z == (res_n * Exp_int(base, exp)) % z,
        decreases exp
    {
        if exp % 2nat == 1nat {
            res_n = (res_n * base) % z;
        }
        exp = exp / 2nat;
        base = (base * base) % z;
    }

    if res_n == 0nat {
        let mut res_v = Vec::new();
        res_v.push('0');
        return res_v;
    }

    let mut temp_n = res_n;
    let mut rev_res = Vec::new();
    while temp_n > 0nat
        invariant
            res_n > 0nat,
            ValidBitString(rev_res@),
            res_n == temp_n * Exp_int(2nat, rev_res@.len() as nat) + Str2Int(rev_res@.reverse()),
        decreases temp_n
    {
        if temp_n % 2nat == 1nat {
            rev_res.push('1');
        } else {
            rev_res.push('0');
        }
        temp_n = temp_n / 2nat;
    }

    let mut res = Vec::new();
    let mut k: usize = 0;
    while k < rev_res.len()
        invariant
            0 <= k <= rev_res.len(),
            ValidBitString(res@),
            res@ == rev_res@.subrange(0, k as int).reverse(),
        decreases rev_res.len() - k
    {
        res.push(rev_res[rev_res.len() - 1 - k]);
        k = k + 1;
    }

    res
}
// </vc-code>

fn main() {}
}
