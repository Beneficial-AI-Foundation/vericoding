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
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let i1 = Str2Int(s1@);
    let i2 = Str2Int(s2@);
    let product = i1 * i2;

    let mut reversed_res = Vec::<char>::new();
    let mut temp = product;

    if temp == 0 {
        reversed_res.push('0');
    } else {
        while temp > 0 {
            let bit = if temp % 2 == 1 { '1' } else { '0' };
            reversed_res.push(bit);
            temp = temp / 2;
        }
    }

    let mut res = Vec::<char>::new();
    let mut i = reversed_res.len() as int - 1;
    while i >= 0 
        invariant 0 <= i + 1 && i + 1 <= reversed_res.len() as int,
        invariant forall |j: int| i + 1 <= j && j < reversed_res.len() as int ==> res@.index(reversed_res.len() as int - 1 - j) == reversed_res@[j],
        invariant res@.len() as int == (reversed_res.len() as int - 1) - i
    {
        res.push(reversed_res@[i]);
        i = i - 1;
    }

    res
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
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    // Base case: y = 0
    if y_int == 0 {
        let mut res = Vec::<char>::new();
        res.push('1');
        return res;
    }

    // Recursive step for y > 0
    let mut s_y_minus_1 = Vec::<char>::new();
    let mut temp_y = y_int;
    let mut leading_zero_index: int = -1;
    proof {
        if y_int > 0 {
            if y_int % 2 == 0 {
                 assert (y_int - 1) == 2 * (y_int / 2) - 1;
            } else {
                 assert (y_int - 1) == 2 * ((y_int - 1)/2);
            }
        }
    }

    if y_int == 1 {
        let mut temp = x_int % z_int;
        let mut reversed_res = Vec::<char>::new();
        if temp == 0 {
            reversed_res.push('0');
        } else {
            while temp > 0 {
                let bit = if temp % 2 == 1 { '1' } else { '0' };
                reversed_res.push(bit);
                temp = temp / 2;
            }
        }
        let mut res = Vec::<char>::new();
        let mut i = reversed_res.len() as int - 1;
        while i >= 0 
            invariant 0 <= i + 1 && i + 1 <= reversed_res.len() as int,
            invariant forall |j: int| i + 1 <= j && j < reversed_res.len() as int ==> res@.index(reversed_res.len() as int - 1 - j) == reversed_res@[j],
            invariant res@.len() as int == (reversed_res.len() as int - 1) - i
        {
            res.push(reversed_res@[i]);
            i = i - 1;
        }
        return res;
    }

    let half_y = y_int / 2;
    let mut reversed_half_y_bits = Vec::<char>::new();
    let mut current_half_y = half_y;
    if current_half_y == 0 {
        reversed_half_y_bits.push('0');
    } else {
        while current_half_y > 0 {
            reversed_half_y_bits.push(if current_half_y % 2 == 1 { '1' } else { '0' });
            current_half_y = current_half_y / 2;
        }
    }
    let mut sy_half_vec = Vec::<char>::new();
    let mut k = reversed_half_y_bits.len() as int - 1;
    while k >= 0 
        invariant 0 <= k + 1 && k + 1 <= reversed_half_y_bits.len() as int,
        invariant forall |j: int| k + 1 <= j && j < reversed_half_y_bits.len() as int ==> sy_half_vec@.index(reversed_half_y_bits.len() as int - 1 - j) == reversed_half_y_bits@[j],
        invariant sy_half_vec@.len() as int == (reversed_half_y_bits.len() as int - 1) - k
    {
        sy_half_vec.push(reversed_half_y_bits@[k]);
        k = k - 1;
    }

    let recur_res = ModExp(sx, &sy_half_vec, sz);
    let recur_res_int = Str2Int(recur_res@);

    let mut square_res = Mul(&recur_res, &recur_res);
    let square_res_int = Str2Int(square_res@);

    let mut r: nat = square_res_int % z_int;
    
    if y_int % 2 == 1 {
        let x_mod_z = x_int % z_int;
        r = (r * x_mod_z) % z_int;
    }

    let mut final_reversed_res = Vec::<char>::new();
    if r == 0 {
        final_reversed_res.push('0');
    } else {
        while r > 0 {
            final_reversed_res.push(if r % 2 == 1 { '1' } else { '0' });
            r = r / 2;
        }
    }

    let mut final_res_vec = Vec::<char>::new();
    let mut m = final_reversed_res.len() as int - 1;
    while m >= 0
        invariant 0 <= m + 1 && m + 1 <= final_reversed_res.len() as int,
        invariant forall |j: int| m + 1 <= j && j < final_reversed_res.len() as int ==> final_res_vec@.index(final_reversed_res.len() as int - 1 - j) == final_reversed_res@[j],
        invariant final_res_vec@.len() as int == (final_reversed_res.len() as int - 1) - m
    {
        final_res_vec.push(final_reversed_res@[m]);
        m = m - 1;
    }

    final_res_vec
}
// </vc-code>

fn main() {}
}
