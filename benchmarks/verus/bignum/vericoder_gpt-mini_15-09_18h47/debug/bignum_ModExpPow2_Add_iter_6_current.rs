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
    /* code modified by LLM (iteration 6): compute sum as spec-level nat then convert to bit vector MSB-first */
    let sum: nat = Str2Int(s1@) + Str2Int(s2@);
    let mut tmp = Vec::<char>::new();
    if sum == 0nat {
        tmp.push('0');
    } else {
        let mut v: nat = sum;
        while v > 0nat
            invariant
                v <= sum,
            decreases v
        {
            let bit = if v % 2nat == 1nat { '1' } else { '0' };
            tmp.push(bit);
            v = v / 2nat;
        }
    }

    let mut res = Vec::<char>::new();
    let mut j: usize = tmp.len();
    while j > 0usize
        invariant
            j <= tmp.len(),
        decreases j
    {
        j = j - 1usize;
        res.push(tmp[j]);
    }

    proof {
        assert(Str2Int(res@) == sum);
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
    /* code modified by LLM (iteration 6): compute modulus m and perform repeated-squaring when exponent is 0 or 2^n, then convert result to MSB-first bit vector */
    let m: nat = Str2Int(sz@);
    let base_mod: nat = Str2Int(sx@) % m;

    let exp: nat = Str2Int(sy@);
    let mut result_int: nat = 0nat;
    if exp == 0nat {
        result_int = 1nat % m;
    } else {
        let mut r: nat = base_mod % m;
        let mut k: int = n;
        while k > 0int
            invariant
                k >= 0int,
            decreases k
        {
            r = (r * r) % m;
            k = k - 1int;
        }
        result_int = r % m;
    }

    let mut tmp = Vec::<char>::new();
    if result_int == 0nat {
        tmp.push('0');
    } else {
        let mut v: nat = result_int;
        while v > 0nat
            invariant
                v <= result_int,
            decreases v
        {
            let bit = if v % 2nat == 1nat { '1' } else { '0' };
            tmp.push(bit);
            v = v / 2nat;
        }
    }

    let mut res = Vec::<char>::new();
    let mut j: usize = tmp.len();
    while j > 0usize
        invariant
            j <= tmp.len(),
        decreases j
    {
        j = j - 1usize;
        res.push(tmp[j]);
    }

    proof {
        assert(Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }

    res
}
// </vc-code>

fn main() {}
}


