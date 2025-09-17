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
/* helper modified by LLM (iteration 2): bit-char utilities and seq->nat conversion */
spec fn bit_char_to_nat(c: char) -> nat
{
    if c == '1' { 1 } else { 0 }
}

spec fn Seq_to_nat(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 0 } else { 2 * Seq_to_nat(s.subrange(0, s.len() as int - 1)) + bit_char_to_nat(s.index(s.len() as int - 1)) }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use usize/u128 runtime arithmetic, avoid nat/int in exec */

    // compute modulus m from sz (runtime u128)
    let mut m: u128 = 0;
    let mut i: usize = 0;
    while i < sz.len()
        invariant
            i <= sz.len(),
        decreases
            sz.len() - i
    {
        let c = sz.get(i);
        if c == '1' {
            m = m * 2 + 1;
        } else {
            m = m * 2;
        }
        i += 1;
    }

    // compute base from sx modulo m
    let mut base: u128 = 0;
    let mut j: usize = 0;
    while j < sx.len()
        invariant
            j <= sx.len(),
        decreases
            sx.len() - j
    {
        let c = sx.get(j);
        base = base * 2 + (if c == '1' { 1 } else { 0 });
        j += 1;
    }

    // Guard: precondition ensures modulus > 1, but check defensively
    if m == 0 {
        return Vec::<char>::new();
    }
    base = base % m;

    // modular exponentiation: square-and-multiply over exponent bits
    let mut res: u128 = 1 % m;
    let mut k: usize = sy.len();
    while k > 0
        invariant
            k <= sy.len(),
        decreases
            k
    {
        k -= 1;
        let b = sy.get(k);
        if b == '1' {
            res = (res * base) % m;
        }
        base = (base * base) % m;
    }

    // convert res to bits (most-significant-first)
    let mut digits = Vec::<char>::new();
    if res == 0 {
        digits.push('0');
    } else {
        let mut x: usize = res as usize;
        while x > 0
            invariant
                x >= 0,
            decreases
                x
        {
            if x % 2 == 1 {
                digits.push('1');
            } else {
                digits.push('0');
            }
            x = x / 2;
        }
    }

    // reverse digits to get most-significant-first output
    let mut out = Vec::<char>::new();
    let mut t: usize = digits.len();
    while t > 0
        invariant
            t <= digits.len(),
        decreases
            t
    {
        t -= 1;
        out.push(digits.get(t));
    }

    return out;
}
// </vc-code>

fn main() {}
}
