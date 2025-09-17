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
    let mut carry = 0;
    let mut i = 0;
    let mut j = 0;
    let mut result_vec = Vec::<char>::new();

    while i < s1.len() || j < s2.len() || carry > 0
        invariant
            carry == 0 || carry == 1,
            (i <= s1.len() && j <= s2.len()) || (carry > 0 && i == s1.len() && j == s2.len()),
            forall |k: int| 0 <= k && k < result_vec.len() ==> (result_vec@[k] == '0' || result_vec@[k] == '1'),
            Str2Int(result_vec@) + carry * Exp_int(2, result_vec.len() as nat) + Str2Int(s1@.subrange(i as int, s1.len() as int)) + Str2Int(s2@.subrange(j as int, s2.len() as int)) == Str2Int(s1@) + Str2Int(s2@)


    {
        let mut digit1 = 0;
        if i < s1.len() {
            digit1 = if s1[s1.len() - 1 - i] == '1' { 1 } else { 0 };
        }

        let mut digit2 = 0;
        if j < s2.len() {
            digit2 = if s2[s2.len() - 1 - j] == '1' { 1 } else { 0 };
        }

        let sum = digit1 + digit2 + carry;
        result_vec.insert(0, if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;

        if i < s1.len() {
            i = i + 1;
        }
        if j < s2.len() {
            j = j + 1;
        }
    }

    // Handle leading zeros if the result is not "0" itself
    while result_vec.len() > 1 && result_vec@[0] == '0' {
        result_vec.remove(0);
    }

    result_vec
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut acc_s = Vec::<char>::new();
    if Mul_helper_is_zero(s1@) || Mul_helper_is_zero(s2@) {
        acc_s.push('0'); // If either operand is 0, the product is 0
    } else {
        acc_s.push('0'); // Initial accumulator value for the sum (0)

        let mut i = 0;
        while i < s2.len()
            invariant
                0 <= i && i <= s2.len(),
                ValidBitString(acc_s@),
                ValidBitString(s1@),
                ValidBitString(s2@),
                Str2Int(acc_s@) == Mul_helper_partial_sum(s1@, s2@, i as nat)
        {
            let s2_bit = if s2[s2.len() - 1 - i] == '1' { 1 } else { 0 };
            if s2_bit == 1 {
                let mut shifted_s1_vec = Vec::<char>::new();
                shifted_s1_vec.extend_from_slice(s1);
                // Add i zeros at the end by converting to char '0'
                let mut k = 0;
                while k < i
                    invariant
                        0 <= k && k <= i,
                        ValidBitString(shifted_s1_vec@),
                        Str2Int(shifted_s1_vec@) == Str2Int(s1@) * Exp_int(2, k as nat)
                {
                    shifted_s1_vec.push('0');
                    k = k + 1;
                }
                acc_s = Add(acc_s.as_slice(), shifted_s1_vec.as_slice());
            }
            i = i + 1;
        }
    }

    acc_s
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
{
    let mut x_nat = Str2Int(sx@);
    let mut y_nat = Str2Int(sy@);
    let mod_nat = Str2Int(sz@);

    let mut result: nat = 1;
    let mut base: nat = x_nat;

    while y_nat > 0
        invariant
            0 <= y_nat,
            base == x_nat * Exp_int(2, (Str2Int(sy@) - y_nat) as nat) % mod_nat,
            result == Exp_int(x_nat, Str2Int(sy@) - y_nat) % mod_nat,
            mod_nat > 1,
            base >= 0,
            result >= 0
    {
        if y_nat % 2 == 1 {
            result = (result * base) % mod_nat;
        }
        base = (base * base) % mod_nat;
        y_nat = y_nat / 2;
    }

    let mut res_vec = Vec::<char>::new();
    if result == 0 {
        res_vec.push('0');
    } else {
        let mut temp_res = result;
        while temp_res > 0
            invariant
                temp_res >= 0,
                forall |k: int| 0 <= k && k < res_vec.len() ==> (res_vec@[k] == '0' || res_vec@[k] == '1'),
                Str2Int(res_vec@) + temp_res * Exp_int(2, res_vec.len() as nat) == result
        {
            if temp_res % 2 == 1 {
                res_vec.insert(0, '1');
            } else {
                res_vec.insert(0, '0');
            }
            temp_res = temp_res / 2;
        }
    }

    // Ensure the result is a valid bit string even if it's 0 initially empty
    if res_vec.is_empty() {
        res_vec.push('0');
    }

    res_vec
}
// </vc-code>

fn main() {}
}
