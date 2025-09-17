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
fn binary_multiply_accumulate(acc: Vec<char>, x: Vec<char>, y: Vec<char>) -> (res: Vec<char>)
    requires
        ValidBitString(acc@),
        ValidBitString(x@),
        ValidBitString(y@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(acc@) + Str2Int(x@) * Str2Int(y@)
{
    if y@.len() == 0 {
        acc
    } else {
        let last_char = y@[y@.len() as int - 1];
        let new_acc = if last_char == '1' {
            binary_add(acc, x)
        } else {
            acc
        };
        let shifted_x = binary_shift_left(x, 1);
        let shifted_y = binary_shift_right(y, 1);
        binary_multiply_accumulate(new_acc, shifted_x, shifted_y)
    }
}

fn binary_add(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
    requires
        ValidBitString(a@),
        ValidBitString(b@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(a@) + Str2Int(b@)
{
    let mut carry = 0;
    let mut result = Vec::new();
    let max_len = if a@.len() > b@.len() { a@.len() } else { b@.len() };
    let mut i = 0;
    while i < max_len || carry > 0
        invariant
            0 <= i,
            ValidBitString(result@),
            carry == 0 || carry == 1,
            Str2Int(result@) + Exp_int(2, i as nat) * carry == Str2Int(a.subrange(0, i)) + Str2Int(b.subrange(0, i)),
        decreases max_len - i + carry
    {
        let bit_a = if i < a@.len() as int { if a@[i] == '1' { 1 } else { 0 } } else { 0 };
        let bit_b = if i < b@.len() as int { if b@[i] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit_a + bit_b + carry;
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        i += 1;
    }
    result
}

fn binary_shift_left(s: Vec<char>, n: nat) -> (res: Vec<char>)
    requires
        ValidBitString(s@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s@) * Exp_int(2, n)
{
    let mut result = s.clone();
    let mut i = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s@) * Exp_int(2, i as nat),
        decreases n - i
    {
        result.push('0');
        i += 1;
    }
    result
}

fn binary_shift_right(s: Vec<char>, n: nat) -> (res: Vec<char>)
    requires
        ValidBitString(s@),
        n <= s@.len(),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s@) / Exp_int(2, n)
{
    let result = s.subrange(0, s@.len() as int - n as int) as Vec<char>;
    result
}

fn binary_mod(a: Vec<char>, m: Vec<char>) -> (res: Vec<char>)
    requires
        ValidBitString(a@),
        ValidBitString(m@),
        Str2Int(m@) > 0,
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(a@) % Str2Int(m@),
        0 <= Str2Int(res@) && Str2Int(res@) < Str2Int(m@)
{
    if Str2Int(a@) < Str2Int(m@) {
        a
    } else {
        let diff = binary_subtract(a, m);
        binary_mod(diff, m)
    }
}

fn binary_subtract(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
    requires
        ValidBitString(a@),
        ValidBitString(b@),
        Str2Int(a@) >= Str2Int(b@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(a@) - Str2Int(b@)
{
    let mut borrow = 0;
    let mut result = Vec::new();
    let max_len = a@.len();
    let mut i = 0;
    while i < max_len
        invariant
            0 <= i && i <= max_len,
            ValidBitString(result@),
            borrow == 0 || borrow == 1,
            Str2Int(a.subrange(0, i)) - Str2Int(b.subrange(0, i)) == Str2Int(result@) - Exp_int(2, i as nat) * borrow,
        decreases max_len - i
    {
        let bit_a = if i < a@.len() as int { if a@[i] == '1' { 1 } else { 0 } } else { 0 };
        let bit_b = if i < b@.len() as int { if b@[i] == '1' { 1 } else { 0 } } else { 0 };
        let diff = bit_a - bit_b - borrow;
        if diff >= 0 {
            result.push(if diff == 1 { '1' } else { '0' });
            borrow = 0;
        } else {
            result.push(if diff + 2 == 1 { '1' } else { '0' });
            borrow = 1;
        }
        i += 1;
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
    let zero_vec = vec!['0'];
    let one_vec = vec!['1'];
    
    if sy@.len() == 0 {
        return one_vec;
    }
    
    let last_char = sy@[sy@.len() as int - 1];
    let shifted_sy = binary_shift_right(Vec::from_slice(sy)?, 1);
    
    let recursive_result = ModExp(
        &binary_mod(Vec::from_slice(sx)?, Vec::from_slice(sz)?).as_slice(),
        &shifted_sy.as_slice(),
        sz
    )?;
    
    let squared_result = binary_mod(
        binary_multiply(recursive_result.clone(), recursive_result),
        Vec::from_slice(sz)?
    );
    
    if last_char == '1' {
        let base_mod = binary_mod(Vec::from_slice(sx)?, Vec::from_slice(sz)?);
        let final_result = binary_mod(
            binary_multiply(squared_result, base_mod),
            Vec::from_slice(sz)?
        );
        final_result
    } else {
        squared_result
    }
}
// </vc-code>

fn main() {}
}
