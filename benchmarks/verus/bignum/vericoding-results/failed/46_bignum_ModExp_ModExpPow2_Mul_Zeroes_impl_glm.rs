// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
    recommends valid_bit_string(s)
    decreases s.len()
{
    if s.len() == 0 { 
        0nat 
    } else { 
        2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}

spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
        str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
        sy.len() == n + 1,
        str2int(sz) > 1
    ensures 
        valid_bit_string(res),
        str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
    decreases n
{
    assume(false);
    unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires valid_bit_string(s1) && valid_bit_string(s2)
    ensures 
        valid_bit_string(res),
        str2int(res) == str2int(s1) * str2int(s2)
{
    assume(false);
    unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
    ensures 
        s.len() == n,
        valid_bit_string(s),
        str2int(s) == 0,
        all_zero(s)
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed return type to i32 and updated ensures clause */
fn vec_binary_compare(a: Vec<char>, b: Vec<char>) -> (cmp: i32)
    requires valid_bit_string(a@) && valid_bit_string(b@)
    ensures (cmp as int) == if str2int(a@) > str2int(b@) { 1 } else if str2int(a@) == str2int(b@) { 0 } else { -1 }
{
    if a.len() > b.len() {
        1
    } else if a.len() < b.len() {
        -1
    } else {
        let mut i = 0usize;
        while i < a.len()
            invariant 0 <= i <= a.len()
            decreases a.len() - i
        {
            if a[i] == '1' && b[i] == '0' {
                return 1;
            } else if a[i] == '0' && b[i] == '1' {
                return -1;
            }
            i += 1;
        }
        0
    }
}

fn vec_binary_sub(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
    requires valid_bit_string(a@) && valid_bit_string(b@) && str2int(a@) >= str2int(b@)
    ensures valid_bit_string(res@) && str2int(res@) == str2int(a@) - str2int(b@)
{
    let mut result_vec: Vec<char> = Vec::new();
    let mut borrow = 0;
    let mut i = if a.len() == 0 { 0 } else { a.len() - 1 };
    let mut j = if b.len() == 0 { 0 } else { b.len() - 1 };
    while i < a.len() || j < b.len() || borrow > 0
        invariant 0 <= borrow <= 1
    {
        let digit_a = if i < a.len() { if a[i] == '1' { 1 } else { 0 } } else { 0 };
        let digit_b = if j < b.len() { if b[j] == '1' { 1 } else { 0 } } else { 0 };
        let diff = digit_a - digit_b - borrow;
        if diff < 0 {
            borrow = 1;
            result_vec.push(if diff + 2 == 1 { '1' } else { '0' });
        } else {
            borrow = 0;
            result_vec.push(if diff == 1 { '1' } else { '0' });
        }
        if i < a.len() { i = if i == 0 { a.len() } else { i - 1 }; }
        if j < b.len() { j = if j == 0 { b.len() } else { j - 1 }; }
    }
    result_vec.reverse();
    let mut start_index = 0usize;
    while start_index < result_vec.len() && result_vec[start_index] == '0' {
        start_index += 1;
    }
    if start_index == result_vec.len() {
        vec!['0']
    } else {
        let mut final_result: Vec<char> = Vec::new();
        let mut k = start_index;
        while k < result_vec.len() {
            final_result.push(result_vec[k]);
            k += 1;
        }
        final_result
    }
}

/* helper modified by LLM (iteration 5): fixed condition to use concrete integer 0 */
fn vec_mod_op(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
    requires valid_bit_string(a@) && valid_bit_string(b@) && str2int(b@) > 0
    ensures valid_bit_string(res@) && str2int(res@) == str2int(a@) % str2int(b@)
{
    let mut current = a;
    while vec_binary_compare(current, b) >= 0
        invariant valid_bit_string(current@)
        decreases (str2int(current@))
    {
        current = vec_binary_sub(current, b);
    }
    current
}

fn vec_mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
    requires valid_bit_string(s1@) && valid_bit_string(s2@)
    ensures valid_bit_string(res@) && str2int(res@) == str2int(s1@) * str2int(s2@)
{
    let mut result = vec_zeros(s1.len() + s2.len());
    let mut i = 0usize;
    while i < s1.len()
        invariant valid_bit_string(result@)
        decreases s1.len() - i
    {
        let mut carry = 0;
        let mut j = 0usize;
        while j < s2.len()
            invariant 0 <= carry <= 1
            decreases s2.len() - j
        {
            let digit1 = if s1[i] == '1' { 1 } else { 0 };
            let digit2 = if s2[j] == '1' { 1 } else { 0 };
            let pos = i + j;
            let current_digit = if result[pos] == '1' { 1 } else { 0 };
            let total = digit1 * digit2 + current_digit + carry;
            carry = total / 2;
            let new_digit = total % 2;
            result[pos] = if new_digit == 1 { '1' } else { '0' };
            j += 1;
        }
        if carry > 0 {
            let pos = i + s2.len();
            let current_digit = if result[pos] == '1' { 1 } else { 0 };
            let total = current_digit + carry;
            carry = total / 2;
            let new_digit = total % 2;
            result[pos] = if new_digit == 1 { '1' } else { '0' };
        }
        i += 1;
    }
    let mut start_index = 0usize;
    while start_index < result.len() && result[start_index] == '0' {
        start_index += 1;
    }
    if start_index == result.len() {
        vec!['0']
    } else {
        let mut final_result: Vec<char> = Vec::new();
        let mut k = start_index;
        while k < result.len() {
            final_result.push(result[k]);
            k += 1;
        }
        final_result
    }
}

fn vec_zeros(n: usize) -> (s: Vec<char>)
    ensures s@.len() == n && valid_bit_string(s@) && str2int(s@) == 0 && all_zero(s@)
{
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n {
        result.push('0');
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        sy.len() > 0 && str2int(sz@) > 1
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
    decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed */
    let base = sx;
    let exponent = sy;
    let modulus = sz;
    let mut result: Vec<char> = vec!['1'];
    let mut i = 0usize;
    while i < exponent.len()
        invariant valid_bit_string(result@)
        decreases exponent.len() - i
    {
        result = vec_mul(result, result);
        result = vec_mod_op(result, modulus);
        if exponent[i] == '1' {
            result = vec_mul(result, base);
            result = vec_mod_op(result, modulus);
        }
        i += 1;
    }
    result
}
// </vc-code>


}

fn main() {}