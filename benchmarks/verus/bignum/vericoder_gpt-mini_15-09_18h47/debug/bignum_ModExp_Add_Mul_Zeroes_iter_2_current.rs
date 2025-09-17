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
/* helper modified by LLM (iteration 2): convert char to numeric bit and back using u8 */
fn char_to_u8(c: char) -> u8 { if c == '1' { 1 } else { 0 } }
fn bit_to_char(b: u8) -> char { if b == 1 { '1' } else { '0' } }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use usize/u128 to avoid nat/int in exec code */

    // compute x_val
    let mut x_val: u128 = 0u128;
    let mut i: usize = 0usize;
    while i < sx.len()
        invariant
            i <= sx.len(),
        decreases sx.len() - i
    {
        let b: u128 = if sx[i] == '1' { 1u128 } else { 0u128 };
        x_val = x_val * 2u128 + b;
        i += 1;
    }

    // compute y_val
    let mut y_val: u128 = 0u128;
    let mut j: usize = 0usize;
    while j < sy.len()
        invariant
            j <= sy.len(),
        decreases sy.len() - j
    {
        let b: u128 = if sy[j] == '1' { 1u128 } else { 0u128 };
        y_val = y_val * 2u128 + b;
        j += 1;
    }

    // compute m_val
    let mut m_val: u128 = 0u128;
    let mut k: usize = 0usize;
    while k < sz.len()
        invariant
            k <= sz.len(),
        decreases sz.len() - k
    {
        let b: u128 = if sz[k] == '1' { 1u128 } else { 0u128 };
        m_val = m_val * 2u128 + b;
        k += 1;
    }

    let orig_x = x_val;
    let orig_y = y_val;

    // modular exponentiation (square-and-multiply) on u128 values
    // m_val is assumed > 1 by the spec precondition
    let mut base: u128 = if m_val == 0u128 { 0u128 } else { orig_x % m_val };
    let mut exp: u128 = orig_y;
    let mut result: u128 = 1u128 % if m_val == 0u128 { 1u128 } else { m_val };
    while exp > 0u128
        invariant
            result < (if m_val == 0u128 { 1u128 } else { m_val }),
        decreases exp
    {
        if (exp & 1u128) == 1u128 {
            result = (result * base) % m_val;
        }
        base = (base * base) % m_val;
        exp = exp >> 1;
    }

    // construct result bitstring (MSB...LSB where last char is LSB)
    let mut resv = Vec::<char>::new();
    if result == 0u128 {
        return resv;
    }

    let mut rev = Vec::<char>::new();
    let mut r: u128 = result;
    while r > 0u128
        invariant
            r >= 0u128,
        decreases r
    {
        let c = if (r & 1u128) == 1u128 { '1' } else { '0' };
        rev.push(c);
        r = r >> 1;
    }

    let mut idx: isize = rev.len() as isize - 1isize;
    while idx >= 0isize
        invariant
            idx >= -1isize,
        decreases idx + 1isize
    {
        resv.push(rev[idx as usize]);
        idx -= 1;
    }

    resv
}
// </vc-code>

fn main() {}
}
