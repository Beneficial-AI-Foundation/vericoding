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
fn slice_to_nat(s: &[char]) -> nat
ensures
    result == Str2Int(s@),
{
    let mut r: nat = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            r == Str2Int(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        let b: nat = if s[i] == '1' { 1 } else { 0 };
        r = 2 * r + b;
        i += 1;
    }
    r
}

fn nat_to_vec(n: nat) -> Vec<char>
    ensures
        ValidBitString(result@),
        Str2Int(result@) == n,
    decreases n
{
    if n == 0 {
        Vec::new()
    } else {
        let mut v = nat_to_vec(n / 2);
        let bit: char = if n % 2 == 1 { '1' } else { '0' };
        v.push(bit);
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x: nat = slice_to_nat(sx);
    let mut y: nat = slice_to_nat(sy);
    let m: nat = slice_to_nat(sz);
    let y0: nat = y;
    let mut res: nat = 1;
    while y > 0
        invariant
            res < m,
            res == Exp_int(x, y0 - y) % m,
        decreases y
    {
        res = (res * x) % m;
        y = y - 1;
    }
    nat_to_vec(res)
}
// </vc-code>

fn main() {}
}
