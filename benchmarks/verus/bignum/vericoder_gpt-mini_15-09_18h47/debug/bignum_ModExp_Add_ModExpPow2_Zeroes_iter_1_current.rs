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
fn slice_to_nat(a: &[char]) -> nat
    ensures
        result == Str2Int(a@),
{
    let mut r: nat = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            r == Str2Int(a@.subrange(0, i as int)),
        decreases a.len() - i
    {
        let bit = a[i];
        if bit == '1' {
            r = 2 * r + 1;
        } else {
            r = 2 * r;
        }
        i += 1;
    }
    r
}

fn nat_to_bitvec_mod(n: nat, base: nat) -> Vec<char>
    requires
        base > 1,
    ensures
        ValidBitString(result@),
        Str2Int(result@) == n % base,
{
    let mut x: nat = n % base;
    let mut v_ls: Vec<char> = Vec::<char>::new();
    if x == 0 {
        v_ls.push('0');
    } else {
        while x > 0
            invariant
                0 <= x,
            decreases x
        {
            if x % 2 == 1 {
                v_ls.push('1');
            } else {
                v_ls.push('0');
            }
            x = x / 2;
        }
    }
    // reverse to get most-significant-first ordering
    let mut v_ms: Vec<char> = Vec::<char>::new();
    let len: usize = v_ls.len();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i && i <= len,
        decreases len - i
    {
        v_ms.push(v_ls[len - 1 - i]);
        i += 1;
    }
    v_ms
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x = slice_to_nat(sx);
    let y = slice_to_nat(sy);
    let m = slice_to_nat(sz);

    // fast modular exponentiation
    let mut base: nat = x % m;
    let mut exp: nat = y;
    let mut acc: nat = 1 % m;

    while exp > 0
        invariant
            0 <= exp,
        decreases exp
    {
        if exp % 2 == 1 {
            acc = (acc * base) % m;
        }
        exp = exp / 2;
        base = (base * base) % m;
    }

    let res = nat_to_bitvec_mod(acc, m);
    res
}
// </vc-code>

fn main() {}
}
