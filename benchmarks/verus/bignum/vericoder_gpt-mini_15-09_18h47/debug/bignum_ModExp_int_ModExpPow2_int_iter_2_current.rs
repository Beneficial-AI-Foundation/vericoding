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
/* helper modified by LLM (iteration 2): convert char to numeric bit */
spec fn CharBit(c: char) -> nat { if c == '1' { 1 } else { 0 } }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int_ModExpPow2_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented modular exponentiation using tracked ghost variables and invariants */

    // compute modulus m = Str2Int(sz@)
    let mut tracked m: nat = 0;
    let mut tracked i: int = 0;
    while i < sz.len() as int
        invariant
            m == Str2Int(sz@.subrange(0, i)),
        decreases (sz.len() as int - i)
    {
        let b = if sz[i as usize] == '1' { 1 } else { 0 };
        m = m * 2 + b;
        i += 1;
    }

    // compute base = Str2Int(sx@)
    let mut tracked base: nat = 0;
    i = 0;
    while i < sx.len() as int
        invariant
            base == Str2Int(sx@.subrange(0, i)),
        decreases (sx.len() as int - i)
    {
        let b = if sx[i as usize] == '1' { 1 } else { 0 };
        base = base * 2 + b;
        i += 1;
    }

    // compute exponent value = Str2Int(sy@)
    let mut tracked exp_val: nat = 0;
    i = 0;
    while i < sy.len() as int
        invariant
            exp_val == Str2Int(sy@.subrange(0, i)),
        decreases (sy.len() as int - i)
    {
        let b = if sy[i as usize] == '1' { 1 } else { 0 };
        exp_val = exp_val * 2 + b;
        i += 1;
    }

    // modular exponentiation using left-to-right binary method
    let mut tracked res_val: nat = 1;
    let base_mod: tracked nat = base % m;
    i = 0;
    while i < sy.len() as int
        invariant
            res_val == Exp_int(base, Str2Int(sy@.subrange(0, i))) % m,
        decreases (sy.len() as int - i)
    {
        // square
        res_val = (res_val * res_val) % m;
        if sy[i as usize] == '1' {
            res_val = (res_val * base_mod) % m;
        }
        i += 1;
    }

    // convert numeric result to bit vector (MSB-first)
    if res_val == 0 {
        return Vec::<char>::new();
    }

    let orig: tracked nat = res_val;
    // find highest power of two <= res_val
    let mut tracked pow: nat = 1;
    while pow <= res_val
        invariant
            pow >= 1,
        decreases (res_val + 1 - pow)
    {
        pow = pow * 2;
    }
    pow = pow / 2;

    let mut tracked acc: nat = 0;
    let mut tracked value: nat = res_val;
    let mut out: Vec<char> = Vec::new();
    while pow > 0
        invariant
            acc == Str2Int(out@),
            orig == acc * (pow * 2) + value,
        decreases pow
    {
        if value >= pow {
            acc = acc * 2 + 1;
            value = value - pow;
            out.push('1');
        } else {
            acc = acc * 2 + 0;
            out.push('0');
        }
        pow = pow / 2;
    }

    return out;
}
// </vc-code>

fn main() {}
}
