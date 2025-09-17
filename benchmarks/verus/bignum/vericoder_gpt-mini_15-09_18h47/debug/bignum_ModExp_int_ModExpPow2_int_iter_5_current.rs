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
/* helper modified by LLM (iteration 5): convert char to numeric bit */
spec fn CharBit(c: char) -> nat { if c == '1' { 1nat } else { 0nat } }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int_ModExpPow2_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix nat/integer mismatches and implement modular exponent and conversion */

    // compute modulus m = Str2Int(sz@)
    let tracked mut m: nat = 0nat;
    let mut i: usize = 0usize;
    while i < sz.len()
        invariant
            m == Str2Int(sz@.subrange(0, i as int)),
        decreases (sz.len() as int - i as int)
    {
        let b: nat = if sz[i] == '1' { 1nat } else { 0nat };
        m = m * 2nat + b;
        i += 1;
    }

    // compute base = Str2Int(sx@)
    let tracked mut base: nat = 0nat;
    i = 0usize;
    while i < sx.len()
        invariant
            base == Str2Int(sx@.subrange(0, i as int)),
        decreases (sx.len() as int - i as int)
    {
        let b: nat = if sx[i] == '1' { 1nat } else { 0nat };
        base = base * 2nat + b;
        i += 1;
    }

    // compute exponent value = Str2Int(sy@)
    let tracked mut exp_val: nat = 0nat;
    i = 0usize;
    while i < sy.len()
        invariant
            exp_val == Str2Int(sy@.subrange(0, i as int)),
        decreases (sy.len() as int - i as int)
    {
        let b: nat = if sy[i] == '1' { 1nat } else { 0nat };
        exp_val = exp_val * 2nat + b;
        i += 1;
    }

    // modular exponentiation using left-to-right binary method (MSB to LSB)
    let tracked mut res_val: nat = 1nat;
    let tracked base_mod: nat = base % m;
    i = 0usize;
    while i < sy.len()
        invariant
            res_val == Exp_int(base, Str2Int(sy@.subrange(0, i as int))) % m,
        decreases (sy.len() as int - i as int)
    {
        // square
        res_val = (res_val * res_val) % m;
        if sy[i] == '1' {
            res_val = (res_val * base_mod) % m;
        }
        i += 1;
    }

    // convert numeric result to bit vector (MSB-first)
    if res_val == 0nat {
        return Vec::<char>::new();
    }

    let tracked orig: nat = res_val;
    // find highest power of two <= res_val
    let tracked mut pow: nat = 1nat;
    while pow <= res_val
        invariant
            pow >= 1nat,
        decreases (res_val + 1nat - pow)
    {
        pow = pow * 2nat;
    }
    pow = pow / 2nat;

    let tracked mut acc: nat = 0nat;
    let tracked mut value: nat = res_val;
    let mut out: Vec<char> = Vec::new();
    while pow > 0nat
        invariant
            acc == Str2Int(out@),
            orig == acc * (pow * 2nat) + value,
        decreases pow
    {
        if value >= pow {
            acc = acc * 2nat + 1nat;
            value = value - pow;
            out.push('1');
        } else {
            acc = acc * 2nat + 0nat;
            out.push('0');
        }
        pow = pow / 2nat;
    }

    return out;
}
// </vc-code>

fn main() {}
}
