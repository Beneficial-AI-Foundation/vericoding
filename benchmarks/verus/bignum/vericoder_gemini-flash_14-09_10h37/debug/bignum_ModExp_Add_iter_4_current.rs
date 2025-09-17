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
/* code modified by LLM (iteration 4): fixed compile errors related to `nat` literals and mismatched types in `Add` function. */
{
    let mut carry: nat = 0; // Fixed: Explicitly declare `carry` as `nat` and initialize with `0`
    let mut res_vec: Vec<char> = Vec::new();
    let mut i: usize = s1.len();
    let mut j: usize = s2.len();

    while i > 0 || j > 0 || carry > 0
        invariant
            i >= 0,
            j >= 0,
            carry == 0 || carry == 1,
            res_vec@.len() <= (s1.len() + s2.len() + 1) as nat,
            ValidBitString(res_vec@)
        decreases i + j + (if carry == 0 { 0 } else { 1 })
    {
        let bit1: nat = if i > 0 { i = i - 1; if s1[i as usize] == '1' { 1 } else { 0 } } else { 0 }; // Fixed: Removed `nat` suffix from literals and added type annotation for `bit1`
        let bit2: nat = if j > 0 { j = j - 1; if s2[j as usize] == '1' { 1 } else { 0 } } else { 0 }; // Fixed: Removed `nat` suffix from literals and added type annotation for `bit2`
        
        let sum_bits: nat = bit1 + bit2 + carry;
        let current_bit: nat = sum_bits % 2;
        carry = sum_bits / 2;

        res_vec.push(if current_bit == 1 { '1' } else { '0' });
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
/* code modified by LLM (iteration 4): Fixed type errors related to `nat` and integer literals. */
{
    let int_sx = Str2Int(sx@);
    let int_sy = Str2Int(sy@);
    let int_sz = Str2Int(sz@);

    let mut acc: nat = 1; // Fixed: Initialized with `1` (nat) directly
    let mut base: nat = int_sx % int_sz;
    let mut power: nat = int_sy;

    while power > 0 // Fixed: `power` is already `nat`
        invariant
            base <= int_sz,
            Exp_int(int_sx, int_sy) % int_sz == (acc * Exp_int(base, power)) % int_sz,
            power >= 0
        decreases power
    {
        if power % 2 == 1 { // Fixed: `power % 2` yields `nat` compatible with `== 1`
            acc = (acc * base) % int_sz;
        }
        base = (base * base) % int_sz;
        power = power / 2; // Fixed: Division yields `nat`
    }

    let mut res_nat = acc;
    let mut res_vec: Vec<char> = Vec::new();

    if res_nat == 0 { // Fixed: `res_nat` is `nat` compatible with `== 0`
        res_vec.push('0');
    } else {
        while res_nat > 0 // Fixed: `res_nat` is `nat` compatible with `> 0`
            invariant
                ValidBitString(res_vec@)
        {
            let bit: nat = res_nat % 2; // Fixed: `bit` is `nat`
            if bit == 1 { // Fixed: `bit` is `nat` compatible with `== 1`
                res_vec.push('1');
            } else {
                res_vec.push('0');
            }
            res_nat = res_nat / 2; // Fixed: Division yields `nat`
        }
        res_vec.reverse();
    }

    res_vec
}
// </vc-code>

fn main() {}
}


