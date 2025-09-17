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
fn char_to_nat(c: char) -> nat { if c == '1' { 1 } else { 0 } }
fn nat_to_char(b: nat) -> char { if b == 1 { '1' } else { '0' } }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // compute x_nat
    let mut x_nat: nat = 0;
    let mut i: int = 0;
    while i < sx.len() as int
        invariant
            0 <= i,
            i <= sx.len() as int,
            x_nat == Str2Int(sx@.subrange(0, i)),
        decreases sx.len() as int - i
    {
        let b = if sx[i as usize] == '1' { 1 } else { 0 };
        x_nat = 2 * x_nat + b;
        i += 1;
    }

    // compute y_nat
    let mut y_nat: nat = 0;
    let mut j: int = 0;
    while j < sy.len() as int
        invariant
            0 <= j,
            j <= sy.len() as int,
            y_nat == Str2Int(sy@.subrange(0, j)),
        decreases sy.len() as int - j
    {
        let b = if sy[j as usize] == '1' { 1 } else { 0 };
        y_nat = 2 * y_nat + b;
        j += 1;
    }

    // compute m_nat
    let mut m_nat: nat = 0;
    let mut k: int = 0;
    while k < sz.len() as int
        invariant
            0 <= k,
            k <= sz.len() as int,
            m_nat == Str2Int(sz@.subrange(0, k)),
        decreases sz.len() as int - k
    {
        let b = if sz[k as usize] == '1' { 1 } else { 0 };
        m_nat = 2 * m_nat + b;
        k += 1;
    }

    let orig_x = x_nat;
    let orig_y = y_nat;

    // modular exponentiation (square-and-multiply)
    let mut base: nat = orig_x % m_nat;
    let mut exp: int = orig_y as int;
    let mut result: nat = 1;
    while exp > 0
        invariant
            exp >= 0,
            result < m_nat,
            base < m_nat,
            (result * Exp_int(base, exp as nat)) % m_nat == Exp_int(orig_x, orig_y) % m_nat,
        decreases exp
    {
        if exp % 2 == 1 {
            result = (result * base) % m_nat;
        }
        base = (base * base) % m_nat;
        exp = exp / 2;
    }

    // construct result bitstring (MSB...LSB where last char is LSB)
    let mut resv = Vec::<char>::new();
    if result == 0 {
        return resv;
    }

    let mut rev = Vec::<char>::new();
    let mut r = result;
    while r > 0
        invariant
            r >= 0,
        decreases r
    {
        let c = if r % 2 == 1 { '1' } else { '0' };
        rev.push(c);
        r = r / 2;
    }

    let mut idx: int = rev.len() as int - 1;
    while idx >= 0
        invariant
            idx >= -1,
            idx < rev.len() as int,
        decreases idx + 1
    {
        resv.push(rev[idx as usize]);
        idx -= 1;
    }

    resv
}
// </vc-code>

fn main() {}
}
