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
{
    let mut result: Vec<char> = Vec::new();
    let mut carry = 0;
    let len1 = s1@.len() as int;
    let len2 = s2@.len() as int;
    let mut i1 = len1 - 1;
    let mut i2 = len2 - 1;
    while i1 >= 0 || i2 >= 0 || carry > 0 {
        let bit1 = if i1 >= 0 {
            if s1@.index(i1) == '1' { 1 } else { 0 }
        } else {
            0
        };
        let bit2 = if i2 >= 0 {
            if s2@.index(i2) == '1' { 1 } else { 0 }
        } else {
            0
        };
        let sum = bit1 + bit2 + carry;
        let new_bit = if sum % 2 == 1 { '1' } else { '0' };
        result.push(new_bit);
        carry = sum / 2;
        i1 -= 1;
        i2 -= 1;
    }
    result.reverse();
    if result.is_empty() {
        result.push('0');
    }
    result
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
    let mut exp_vec = sy.iter().cloned().collect::<Vec<_>>();
    let mut base_vec = sx.iter().cloned().collect::<Vec<_>>();
    let sz_vec = sz.iter().cloned().collect::<Vec<_>>();
    let mut res_vec = vec!['1'];
    let add = |a: &Vec<char>, b: &Vec<char>| -> Vec<char> {
        let mut result = Vec::new();
        let mut carry = 0;
        let mut i1 = a.len() as isize - 1;
        let mut i2 = b.len() as isize - 1;
        while i1 >= 0 || i2 >= 0 || carry > 0 {
            let bit1 = if i1 >= 0 {
                if a[i1 as usize] == '1' { 1 } else { 0 }
            } else {
                0
            };
            let bit2 = if i2 >= 0 {
                if b[i2 as usize] == '1' { 1 } else { 0 }
            } else {
                0
            };
            let sum = bit1 + bit2 + carry;
            let new_bit = if sum % 2 == 1 { '1' } else { '0' };
            result.push(new_bit);
            carry = sum / 2;
            i1 -= 1;
            i2 -= 1;
        }
        result.reverse();
        if result.is_empty() {
            result.push('0');
        }
        result
    };
    let ge = |a: &Vec<char>, b: &Vec<char>| -> bool {
        if a.len() != b.len() {
            a.len() > b.len()
        } else {
            for i in 0..a.len() {
                if a[i] != b[i] {
                    return a[i] > b[i];
                }
            }
            true
        }
    };
    let sub = |a: &Vec<char>, b: &Vec<char>| -> Vec<char> {
        let mut result = Vec::new();
        let mut borrow = 0;
        let mut i1 = a.len() as isize - 1;
        let mut i2 = b.len() as isize - 1;
        while i1 >= 0 {
            let bit1 = if a[i1 as usize] == '1' { 1 } else { 0 };
            let bit2 = if i2 >= 0 { if b[i2 as usize] == '1' { 1 } else { 0 } } else { 0 };
            let diff = bit1 - bit2 - borrow;
            borrow = if diff < 0 { 1 } else { 0 };
            let new_bit = if (diff + 2) % 2 == 1 { '1' } else { '0' };
            result.push(new_bit);
            i1 -= 1;
            i2 -= 1;
        }
        result.reverse();
        while result.len() > 1 && result[0] == '0' {
            result.remove(0);
        }
        result
    };
    let mul = |a: &Vec<char>, b: &Vec<char>| -> Vec<char> {
        let mut result = vec!['0'];
        for i in 0..b.len() {
            if b[i] == '1' {
                let mut shifted_a = a.clone();
                for _ in 0..i {
                    shifted_a.push('0');
                }
                result = add(&result, &shifted_a);
            }
        }
        result
    };
    let mod_fn = |a: &Vec<char>, b: &Vec<char>| -> Vec<char> {
        let mut result = a.clone();
        while ge(&result, b) {
            result = sub(&result, b);
        }
        result
    };
    base_vec = mod_fn(&base_vec, &sz_vec);
    res_vec = mod_fn(&res_vec, &sz_vec);
    while !exp_vec.is_empty() {
        if exp_vec[exp_vec.len() - 1] == '1' {
            let t = mul(&res_vec, &base_vec);
            res_vec = mod_fn(&t, &sz_vec);
        }
        let t = mul(&base_vec, &base_vec);
        base_vec = mod_fn(&t, &sz_vec);
        exp_vec.truncate(exp_vec.len() - 1);
    }
    res_vec
}
// </vc-code>

fn main() {}
}


