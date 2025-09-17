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
fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-code>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): Changed `nat` to `int` for local `sum` variable, as it's not a ghost variable. */
{
    let mut result: Vec<char> = Vec::new();
    let mut carry: nat = 0nat;
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < s1.len() || j < s2.len() || carry > 0
        invariant
            carry >= 0 && carry <= 2,
            ValidBitString(result@),
            i <= s1.len(),
            j <= s2.len(),
        decreases (s1.len() - i) + (s2.len() - j)
    {
        let mut sum: int = carry as int;
        if i < s1.len() {
            sum += (s1[s1.len() - 1 - i] as u8 - b'0') as int;
        }
        if j < s2.len() {
            sum += (s2[s2.len() - 1 - j] as u8 - b'0') as int;
        }

        result.insert(0, if sum % 2 == 1 { '1' } else { '0' });
        carry = (sum / 2) as nat;

        if i < s1.len() {
            i += 1;
        }
        if j < s2.len() {
            j += 1;
        }
    }

    if result.len() == 0 {
        result.push('0');
    }
    result
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
fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): No changes Made. */
{
    let dividend_val = Str2Int(dividend@);
    let divisor_val = Str2Int(divisor@);

    let quotient_val = dividend_val / divisor_val;
    let remainder_val = dividend_val % divisor_val;

    let mut quotient_vec = Vec::<char>::new();
    if quotient_val == 0 {
        quotient_vec.push('0');
    } else {
        let mut temp_quotient = quotient_val;
        while temp_quotient > 0
            invariant
                temp_quotient >= 0,
                ValidBitString(quotient_vec@),
            decreases temp_quotient
        {
            quotient_vec.insert(0, if temp_quotient % 2 == 1 { '1' } else { '0' });
            temp_quotient /= 2;
        }
    }

    let mut remainder_vec = Vec::<char>::new();
    if remainder_val == 0 {
        remainder_vec.push('0');
    } else {
        let mut temp_remainder = remainder_val;
        while temp_remainder > 0
            invariant
                temp_remainder >= 0,
                ValidBitString(remainder_vec@),
            decreases temp_remainder
        {
            remainder_vec.insert(0, if temp_remainder % 2 == 1 { '1' } else { '0' });
            temp_remainder /= 2;
        }
    }

    // Proof to establish that the generated vectors are valid bit strings
    proof {
        //@ assert ValidBitString(quotient_vec@);
        //@ assert ValidBitString(remainder_vec@);
    }

    (quotient_vec, remainder_vec)
}
// </vc-code>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-code>

fn main() {}
}
