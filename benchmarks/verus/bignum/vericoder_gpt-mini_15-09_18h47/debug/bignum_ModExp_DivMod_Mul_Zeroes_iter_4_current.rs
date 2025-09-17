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
/* helper modified by LLM (iteration 4): alias for Str2Int */
spec fn bits_to_nat(s: Seq<char>) -> nat { Str2Int(s) }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): replaced unsupported `while let` with index-based pop and used division-based bit ops */
    let mut x: u128 = 0u128;
    let mut i: usize = 0usize;
    while i < sx.len() {
        let c = sx[i];
        x = x * 2u128 + (if c == '1' { 1u128 } else { 0u128 });
        i += 1usize;
    }

    let mut y: u128 = 0u128;
    i = 0usize;
    while i < sy.len() {
        let c = sy[i];
        y = y * 2u128 + (if c == '1' { 1u128 } else { 0u128 });
        i += 1usize;
    }

    let mut m: u128 = 0u128;
    i = 0usize;
    while i < sz.len() {
        let c = sz[i];
        m = m * 2u128 + (if c == '1' { 1u128 } else { 0u128 });
        i += 1usize;
    }

    if m == 0u128 {
        return Vec::<char>::new();
    }

    let mut base: u128 = x % m;
    let mut exp: u128 = y;
    let mut res_n: u128 = 1u128 % m;

    while exp > 0u128 {
        if exp % 2u128 == 1u128 {
            res_n = (res_n * base) % m;
        }
        base = (base * base) % m;
        exp = exp / 2u128;
    }

    let mut out = Vec::<char>::new();
    if res_n == 0u128 {
        return out;
    }

    let mut tmp = Vec::<char>::new();
    while res_n > 0u128 {
        let b = if res_n % 2u128 == 1u128 { '1' } else { '0' };
        tmp.push(b);
        res_n = res_n / 2u128;
    }

    while tmp.len() > 0 {
        let last = tmp.len() - 1;
        let ch = tmp[last];
        tmp.pop();
        out.push(ch);
    }

    out
}
// </vc-code>

fn main() {}
}
