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
/* code modified by LLM (iteration 4): Fixed the loop invariant for binary addition to correctly track the sum. */
{
    let mut carry = 0;
    let mut i = 0;
    let mut j = 0;
    let mut result_vec: Vec<char> = Vec::new();

    while i < s1.len() || j < s2.len() || carry > 0
        invariant
            carry == 0 || carry == 1,
            0 <= i && i <= s1.len(),
            0 <= j && j <= s2.len(),
            ValidBitString(result_vec@),
            Str2Int(result_vec@) == (Str2Int(s1@.subrange(s1.len() as int - i as int, s1.len() as int)) + Str2Int(s2@.subrange(s2.len() as int - j as int, s2.len() as int)) + carry as nat) % Exp_int(2, (result_vec.len()) as nat),

    {
        let mut digit1: nat = 0;
        if i < s1.len() {
            digit1 = if s1[s1.len() - 1 - i] == '1' { 1 } else { 0 };
        }

        let mut digit2: nat = 0;
        if j < s2.len() {
            digit2 = if s2[s2.len() - 1 - j] == '1' { 1 } else { 0 };
        }

        let sum = digit1 + digit2 + carry as nat;
        result_vec.insert(0, if sum % 2 == 1 { '1' } else { '0' });
        carry = (sum / 2) as int;

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
/* helper modified by LLM (iteration 4): Fixed the syntax error by adding curly braces to the spec fn. */
spec fn Mul_helper_is_zero(s: Seq<char>) -> bool
{
    Str2Int(s) == 0
}

/* helper modified by LLM (iteration 4): Fixed the loop invariant in Mul_helper_partial_sum to correctly track the sum. */
spec fn Mul_helper_partial_sum(s1: Seq<char>, s2: Seq<char>, i: nat) -> nat {
    let mut sum: nat = 0;
    let mut k: nat = 0;

    while k < i
        invariant
            0 <= k && k <= i,
            sum == (0..k).map(|x:nat| 
                        if (s2.len() as int) - 1 - (x as int) >= 0 
                        && (s2.len() as int) - 1 - (x as int) < s2.len() 
                        && s2[(s2.len() - 1 - x) as int] == '1' 
                        { Str2Int(s1) * Exp_int(2, x) } else { 0nat } ).fold(0, |acc, val| acc + val)

    {
        let s2_bit_val = if (s2.len() as int) - 1 - (k as int) >= 0 && (s2.len() as int) - 1 - (k as int) < s2.len() && s2[(s2.len() - 1 - k) as int] == '1' { 1 } else { 0 };
        if s2_bit_val == 1 {
            sum = sum + Str2Int(s1) * Exp_int(2, k);
        }
        k = k + 1;
    }
    sum
}

/* code modified by LLM (iteration 4): Corrected the loop invariant for multiplication and shifted_s1_vec. */
{
    let mut acc_s = Vec::<char>::new();
    if Mul_helper_is_zero(s1@) || Mul_helper_is_zero(s2@) {
        acc_s.push('0'); // If either operand is 0, the product is 0
    } else {
        acc_s.push('0'); // Initial accumulator value for the sum (0)

        let mut i: nat = 0;
        while i < s2.len()
            invariant
                0 <= i && i <= s2.len(),
                ValidBitString(acc_s@),
                ValidBitString(s1@),
                ValidBitString(s2@),
                Str2Int(acc_s@) == Mul_helper_partial_sum(s1@, s2@, i)
        {
            let s2_bit = if (s2.len() as int) - 1 - (i as int) >= 0 && (s2.len() as int) - 1 - (i as int) < s2.len() && s2[(s2.len() - 1 - i) as int] == '1' { 1 } else { 0 };
            if s2_bit == 1 {
                let mut shifted_s1_vec = Vec::<char>::new();
                shifted_s1_vec.extend_from_slice(s1);
                let mut k: nat = 0;
                while k < i
                    invariant
                        0 <= k && k <= i,
                        ValidBitString(shifted_s1_vec@),
                        Str2Int(shifted_s1_vec@) == Str2Int(s1@) * Exp_int(2, k)
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
/* code modified by LLM (iteration 4): Fixed the loop invariant for ModExpPow2's main loop and the `result_vec` conversion. */
{
    let x_nat = Str2Int(sx@);
    let y_nat = Str2Int(sy@);
    let mod_nat = Str2Int(sz@);

    let mut result: nat = 1;
    let mut base: nat = x_nat % mod_nat;
    let mut y_temp: nat = y_nat;

    while y_temp > 0
        invariant
            y_temp >= 0,
            base >= 0,
            result >= 0,
            mod_nat > 1,
            (result * Exp_int(x_nat % mod_nat, y_temp)) % mod_nat == Exp_int(x_nat, y_nat) % mod_nat
    {
        if y_temp % 2 == 1 {
            result = (result * base) % mod_nat;
        }
        base = (base * base) % mod_nat;
        y_temp = y_temp / 2;
    }

    let mut res_vec = Vec::<char>::new();
    if result == 0 {
        res_vec.push('0');
    } else {
        let mut temp_pow_val: nat = 1;
        let mut current_result_value: nat = 0;
        let mut temp_result = result;
        while temp_result > 0
            invariant
                temp_result >= 0,
                ValidBitString(res_vec@),
                current_result_value == result % temp_pow_val,
                temp_pow_val == Exp_int(2, res_vec.len() as nat)
        {
            if temp_result % 2 == 1 {
                res_vec.insert(0, '1');
            } else {
                res_vec.insert(0, '0');
            }
            temp_result = temp_result / 2;
            temp_pow_val = temp_pow_val * 2;
            current_result_value = current_result_value + (if res_vec@[0] == '1' { temp_pow_val / 2 } else { 0 });
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
