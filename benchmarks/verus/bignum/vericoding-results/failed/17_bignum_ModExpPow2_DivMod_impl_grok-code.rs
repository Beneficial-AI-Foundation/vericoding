// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        if valid_bit_string(s) {
            2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
        } else {
            0nat
        }
    }
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
    requires 
        valid_bit_string(dividend) && valid_bit_string(divisor) && str2int(divisor) > 0
    ensures 
        valid_bit_string(result.0) && valid_bit_string(result.1),
        str2int(result.0) == str2int(dividend) / str2int(divisor),
        str2int(result.1) == str2int(dividend) % str2int(divisor)
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 6): fixed Seq construction to empty and type casting for nat/int comparisons and indexing */
spec fn bit_string_add_pad(s1: Seq<char>, s2: Seq<char>, carry_in: int) -> Seq<char>
    requires
        valid_bit_string(s1),
        valid_bit_string(s2),
        s1.len() == s2.len(),
        carry_in == 0 || carry_in == 1
    ensures
        valid_bit_string(result),
        result.len() == s1.len() || result.len() == s1.len() + 1,
        str2int(result) == str2int(s1) + str2int(s2) + carry_out as nat  // but need to define carry as 0
    decreases s1.len()
{
    if s1.len() == 0 {
        if carry_in == 1 { Seq::cons('1', Seq::empty()) } else { Seq::empty() }
    } else {
        let bit1 = if s1[s1.len() - 1] == '1' { 1 } else { 0 };
        let bit2 = if s2[s2.len() - 1] == '1' { 1 } else { 0 };
        let sum = bit1 + bit2 + carry_in;
        let new_carry = sum / 2;
        let new_bit = if sum % 2 == 1 { '1' } else { '0' };
        let rest = bit_string_add_pad(s1.subrange(0, s1.len() - 1), s2.subrange(0, s2.len() - 1), new_carry);
        rest.push(new_bit)
    }
}

spec fn bit_string_add(a: Seq<char>, b: Seq<char>) -> Seq<char>
    requires
        valid_bit_string(a),
        valid_bit_string(b)
    ensures
        valid_bit_string(result),
        str2int(result) == str2int(a) + str2int(b)
{
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    let a_padded = bit_string_pad_zero(a, max_len - a.len());
    let b_padded = bit_string_pad_zero(b, max_len - b.len());
    bit_string_add_pad(a_padded, b_padded, 0)
}

spec fn bit_string_pad_zero(s: Seq<char>, num_zeros: nat) -> Seq<char>
    requires valid_bit_string(s)
    ensures valid_bit_string(result)
    decreases num_zeros
{
    if num_zeros == 0 { s } else { bit_string_pad_zero(Seq::cons('0', s), num_zeros - 1) }
}

spec fn bit_string_mul_pad(a: Seq<char>, b: Seq<char>, mul_pos: nat, acc: Seq<char>) -> Seq<char>
    requires
        valid_bit_string(a),
        valid_bit_string(b)
    ensures
        valid_bit_string(result),
        str2int(result) == str2int(acc) + str2int(b.subrange(0, b.len() - mul_pos)) * str2int(a) * exp_int(2nat, mul_pos)  // approximate
    decreases mul_pos
{
    if mul_pos >= b.len() { acc } else {
        if b[b.len() - 1 - mul_pos] == '1' {
            let shifted_a = bit_string_shift_left(a, mul_pos as int);
            bit_string_mul_pad(a, b, mul_pos + 1, bit_string_add(acc, shifted_a))
        } else {
            bit_string_mul_pad(a, b, mul_pos + 1, acc)
        }
    }
}

spec fn bit_string_shift_left(s: Seq<char>, amount: int) -> Seq<char>
    requires valid_bit_string(s), amount >= 0
    ensures valid_bit_string(result)
    decreases amount
{
    if amount == 0 { s } else { bit_string_shift_left(s.push('0'), amount - 1) }
}

spec fn bit_string_mul(a: Seq<char>, b: Seq<char>) -> Seq<char>
    requires
        valid_bit_string(a),
        valid_bit_string(b)
    ensures
        valid_bit_string(result),
        str2int(result) == str2int(a) * str2int(b)
{
    bit_string_mul_pad(a, b, 0nat, Seq::empty())
}

spec fn bit_string_mod_mul(a: Seq<char>, b: Seq<char>, modd: Seq<char>) -> Seq<char>
    requires
        valid_bit_string(a),
        valid_bit_string(b),
        valid_bit_string(modd),
        str2int(modd) > 0
    ensures
        valid_bit_string(result),
        str2int(result) == (str2int(a) * str2int(b)) % str2int(modd)
{
    let product = bit_string_mul(a, b);
    let (quot, rem) = div_mod(product, modd);
    rem
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0,
        sy.len() == n as int + 1,
        str2int(sz@) > 1
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
    decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 6): added type casting for seq len and indexing */
    let mut sy_is_zero = true;
    let mut i: usize = 0;
    while i < sy.len() {
        if sy[i] != '0' {
            sy_is_zero = false;
        }
        i = i + 1;
    }
    if sy_is_zero {
        return vec!['1'];
    }
    let (sx_quot, sx_rem) = div_mod(sx@, sz@);
    let mut sx_rem_vec: Vec<char> = Vec::new();
    let mut i1: int = 0;
    while i1 < sx_rem.len() as int {
        sx_rem_vec.push(sx_rem[i1]);
        i1 = i1 + 1;
    }
    let mut result = sx_rem_vec;
    let mut k: usize = 0;
    while k < (n as usize) {
        let big_prod = bit_string_mul(result@, result@);
        let (_, rem) = div_mod(big_prod, sz@);
        let mut rem_vec: Vec<char> = Vec::new();
        let mut j: int = 0;
        while j < rem.len() as int {
            rem_vec.push(rem[j]);
            j = j + 1;
        }
        result = rem_vec;
        k = k + 1;
    }
    result
}
// </vc-code>


}

fn main() {}