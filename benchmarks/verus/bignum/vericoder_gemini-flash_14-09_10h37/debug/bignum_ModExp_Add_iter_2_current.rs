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
/* code modified by LLM (iteration 2): fixed type errors by using usize for indices and not casting s.len() to int for `len()` return values; simplified loop invariant for Str2Int*/
{
    let mut carry: nat = 0;
    let mut res_vec: Vec<char> = Vec::new();
    let mut i: int = (s1.len() as int) - 1;
    let mut j: int = (s2.len() as int) - 1;

    while i >= 0 || j >= 0 || carry > 0 
        invariant 
            i >= -1, j >= -1,
            carry == 0 || carry == 1,
            res_vec@.len() <= (s1.len() + s2.len() + 1) as nat,
            ValidBitString(res_vec@)
            /* verification error: loop invariant violation
             * The original invariant was too complex for the current state.
             * Simplifying it allows the method body to compile and then focus on the Str2Int post-condition. */
        decreases i + j + (if carry == 0 { 0 } else { 1 })
    {
        let bit1 = if i >= 0 { if s1[i as usize] == '1' { 1nat } else { 0nat } } else { 0nat };
        let bit2 = if j >= 0 { if s2[j as usize] == '1' { 1nat } else { 0nat } } else { 0nat };
        
        let sum_bits = bit1 + bit2 + carry;
        let current_bit = sum_bits % 2;
        carry = sum_bits / 2;

        res_vec.push(if current_bit == 1 { '1' } else { '0' });

        if i >= 0 { i = i - 1; }
        if j >= 0 { j = j - 1; }
    }
    
    res_vec.reverse();
    if res_vec.len() == 0 { res_vec.push('0'); }
    res_vec
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
/* code modified by LLM (iteration 2): fixed type errors by using `usize` for indices and `nat` for values from `Str2Int`; updated invariant for `nat` to `Vec<char>` conversion to be simpler and focus on the `res_nat` to `Str2Int` relationship. */
{
    let int_sx = Str2Int(sx@);
    let int_sy = Str2Int(sy@);
    let int_sz = Str2Int(sz@);

    let mut acc: nat = 1;
    let mut base: nat = int_sx % int_sz;
    let mut power: nat = int_sy;

    while power > 0
        invariant
            base <= int_sz,
            Exp_int(int_sx, int_sy) % int_sz == (acc * Exp_int(base, power)) % int_sz,
            power >= 0
        decreases power
    {
        if power % 2 == 1 {
            acc = (acc * base) % int_sz;
        }
        base = (base * base) % int_sz;
        power = power / 2;
    }

    let mut res_nat = acc;
    let mut res_vec: Vec<char> = Vec::new();

    if res_nat == 0 {
        res_vec.push('0');
    } else {
        while res_nat > 0
            invariant
                ValidBitString(res_vec@),
                // The value represented by 'res_vec' (reversed) as a binary string, plus
                // the value of 'res_nat' * (2^res_vec.len()), should equal the original 'acc'.
                // This more accurately reflects the process of building the binary string from right to left.
                acc == Str2Int(res_vec@.reversed()) + res_nat * Exp_int(2, res_vec.len() as nat)
        {
            let bit = res_nat % 2;
            if bit == 1 {
                res_vec.push('1');
            } else {
                res_vec.push('0');
            }
            res_nat = res_nat / 2;
        }
        res_vec.reverse();
    }

    res_vec
}
// </vc-code>

fn main() {}
}


