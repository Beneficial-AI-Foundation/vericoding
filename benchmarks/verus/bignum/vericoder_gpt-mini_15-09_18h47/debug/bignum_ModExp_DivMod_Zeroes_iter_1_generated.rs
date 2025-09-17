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
spec fn NatToSeq(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        let s = NatToSeq(n / 2);
        // append least-significant bit
        s + Seq::from_slice(&(if n % 2 == 1 { vec!['1'] } else { vec!['0'] }))
    }
}

proof fn NatToSeq_correct(n: nat) ensures Str2Int(NatToSeq(n)) == n
    decreases n
{
    if n == 0 {
        // Str2Int(Seq::empty()) == 0 by definition
    } else {
        NatToSeq_correct(n / 2);
        // from definition of NatToSeq and Str2Int, Str2Int(s + [b]) == 2 * Str2Int(s) + (b=='1')
    }
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
    // compute modulus
    let m: nat = Str2Int(sz@);

    // base and result as nats modulo m
    let mut base: nat = Str2Int(sx@) % m;
    let mut res_nat: nat = 1 % m;

    // iterate exponent bits from least-significant (last) to most-significant (first)
    let mut idx: int = sy@.len() as int - 1;
    while idx >= 0
        invariant
            -1 <= idx,
        decreases idx + 1
    {
        let b: char = sy@.index(idx);
        if b == '1' {
            res_nat = (res_nat * base) % m;
        }
        base = (base * base) % m;
        idx -= 1;
    }

    // convert res_nat to bits (LSB first)
    let mut digits = Vec::<char>::new();
    if res_nat == 0 {
        digits.push('0');
    } else {
        let mut x: nat = res_nat;
        while x > 0
            invariant
                x >= 0,
            decreases x
        {
            if x % 2 == 1 {
                digits.push('1');
            } else {
                digits.push('0');
            }
            x = x / 2;
        }
    }

    // reverse digits to get most-significant-first sequence
    let mut out = Vec::<char>::new();
    let mut j: usize = digits.len();
    while j > 0
        invariant
            j <= digits.len(),
        decreases j
    {
        j -= 1;
        out.push(digits.get(j));
    }

    return out;
}
// </vc-code>

fn main() {}
}
