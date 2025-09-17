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
exec fn pad_front_zero(v: &Vec<char>, len: usize) -> Vec<char> {
    let mut res = Vec :: with_capacity(len);
    let n_zeros = len.checked_sub(v.len()).unwrap_or(0);
    for _ in 0..n_zeros {
        res.push('0');
    }
    res.extend_from_slice(v);
    res
}

exec fn big_less(a: &Vec<char>, b: &Vec<char>) -> bool {
    if a.len() < b.len() {
        true
    } else if a.len() > b.len() {
        false
    } else {
        let mut i = 0;
        while i < a.len() {
            if a[i] < b[i] {
                return true;
            }
            if a[i] > b[i] {
                return false;
            }
            i += 1;
        }
        false
    }
}

exec fn big_ge(a: &Vec<char>, b: &Vec<char>) -> bool {
    !big_less(a, b)
}

exec fn big_zero() -> Vec<char> {
    vec!['0']
}

exec fn big_one() -> Vec<char> {
    vec!['1']
}

exec fn big_add(a: &Vec<char>, b: &Vec<char>) -> Vec<char> {
    let max_len = a.len().max(b.len());
    let a_pad = pad_front_zero(a, max_len);
    let b_pad = pad_front_zero(b, max_len);
    let mut result = Vec::new();
    let mut carry = 0;
    let mut i = max_len;
    while i > 0 {
        i -= 1;
        let ai = a_pad[i] as u8 - b'0';
        let bi = b_pad[i] as u8 - b'0';
        let sum = (ai + bi + carry) as u8;
        result.insert(0, (sum % 2 + b'0') as char);
        carry = sum / 2;
    }
    if carry > 0 {
        result.insert(0, '1');
    }
    if result.len() > 1 && result[0] == '0' {
        let mut j = 0;
        while j < result.len() - 1 && result[j] == '0' {
            j += 1;
        }
        let mut trimmed = Vec::new();
        for k in j..result.len() {
            trimmed.push(result[k]);
        }
        trimmed
    } else {
        result
    }
}

exec fn shift_left(v: &Vec<char>, n: usize) -> Vec<char> {
    let mut res = v.clone();
    for _ in 0..n {
        res.push('0');
    }
    res
}

exec fn big_mul(a: &Vec<char>, b: &Vec<char>) -> Vec<char> {
    let mut result = vec!['0'];
    let mut shift = 0;
    let mut i = a.len();
    while i > 0 {
        i -= 1;
        shift += 1;
        if a[i] == '1' {
            let shifted = shift_left(b, a.len() - 1 - i);
            result = big_add(&result, &shifted);
        }
    }
    result
}

exec fn big_sub(a: Vec<char>, b: &Vec<char>) -> Vec<char> {
    // assume a > b or equal, but for mod, a >= b
    let mut result = Vec::new();
    let mut borrow = 0i8;
    let len = a.len();
    let blen = b.len();
    let mut i = len;
    while i > 0 {
        i -= 1;
        let ai = (a[i] as u8 - b'0') as i8;
        let bi = if i >= len - blen { (b[i - (len - blen)] as u8 - b'0') as i8 } else { 0 };
        let mut diff = ai - bi - borrow;
        if diff < 0 {
            diff += 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        result.insert(0, (diff as u8 + b'0') as char);
    }
    if result.len() > 1 && result[0] == '0' {
        let mut j = 0;
        while j < result.len() - 1 && result[j] == '0' {
            j += 1;
        }
        let mut trimmed = Vec::new();
        for k in j..result.len() {
            trimmed.push(result[k]);
        }
        trimmed
    } else {
        result
    }
}

exec fn big_mod(rem: Vec<char>, modulator: &Vec<char>) -> Vec<char> {
    let mut current = rem;
    while big_ge(&current, modulator) {
        current = big_sub(current, modulator);
    }
    current
}

exec fn big_mul_mod(a: &Vec<char>, b: &Vec<char>, m: &Vec<char>) -> Vec<char> {
    let product = big_mul(a, b);
    big_mod(product, m)
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        big_one()
    } else {
        let last = sy[sy.len() - 1];
        let prefix: &[char] = &sy[0..sy.len() - 1];
        let half = ModExp_Zeroes(sx, prefix, sz);
        let square = big_mul_mod(&half, &half, &sz.to_vec());
        if last == '1' {
            let sx_mod = big_mod(sx.to_vec(), &sz.to_vec());
            big_mul_mod(&square, &sx_mod, &sz.to_vec())
        } else {
            square
        }
    }
}
// </vc-code>

fn main() {}
}
