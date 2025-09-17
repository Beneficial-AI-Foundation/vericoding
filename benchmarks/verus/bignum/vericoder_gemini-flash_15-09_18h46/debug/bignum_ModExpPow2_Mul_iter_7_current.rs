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
/* code modified by LLM (iteration 7): Cast product to u128 using `as u128` instead of `into()` and compared `nat` to `0nat`. */
{
    let n1 = Str2Int(s1@);
    let n2 = Str2Int(s2@);
    let product = n1 * n2;

    let mut result: Vec<char> = Vec::new();
    let mut temp: u128;

    if product == 0nat {
        temp = 0;
    } else {
        temp = product as u128;
    }

    if temp == 0 {
        result.push('0');
        return result;
    }

    while temp > 0
        invariant
            temp >= 0,
            Str2Int(result@) * Exp_int(2, result@.len() as nat) + temp as nat == product
        decreases temp
    {
        if temp % 2 == 1 {
            result.insert(0, '1');
        } else {
            result.insert(0, '0');
        }
        temp = temp / 2;
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
/* code modified by LLM (iteration 7): Cast nat values to u128 using `as u128`. Corrected comparison of `nat` to `0nat` and `int` to `0`. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    if n == 0 {
        let mut res = Vec::new();
        res.push('0'); // Should be '1' because x^0 = 1
        return res;
    }

    if y_int == 0nat {
        let mut res = Vec::new();
        res.push('1');
        return res;
    }

    let mut current_exp_val: nat = x_int;
    let mut k: u128 = 0;
    let n_u128: u128 = n as u128;

    while k < n_u128
        invariant
            current_exp_val == Exp_int(x_int, Exp_int(2, k as nat)) % z_int,
            k as int >= 0,
            k <= n_u128
        decreases (n_u128 - k)
    {
        current_exp_val = (current_exp_val * current_exp_val) % z_int;
        k = k + 1;
    }

    let final_val = current_exp_val;

    let mut result_vec = Vec::new();
    let mut temp: u128;

    if final_val == 0nat {
        temp = 0;
    } else {
        temp = final_val as u128;
    }

    if temp == 0 {
        result_vec.push('0');
        return result_vec;
    }

    while temp > 0
        invariant
            temp >= 0,
            Str2Int(result_vec@) * Exp_int(2, result_vec@.len() as nat) + (temp as nat) == final_val
        decreases temp
    {
        if temp % 2 == 1 {
            result_vec.insert(0, '1');
        } else {
            result_vec.insert(0, '0');
        }
        temp = temp / 2;
    }
    result_vec
}
// </vc-code>

fn main() {}
}


