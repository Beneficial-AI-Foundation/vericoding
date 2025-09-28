// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
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

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
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
/* helper modified by LLM (iteration 4): fixed slice expressions in invariants */
fn create_zeros(n: usize) -> (s: Vec<char>)
    ensures
        s@.len() == n as nat,
        valid_bit_string(s@),
        str2int(s@) == 0,
        all_zero(s@)
{
    let mut vec = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            vec.len() == i,
            all_zero(vec@),
            str2int(vec@) == 0
        decreases n - i
    {
        vec.push('0');
        i += 1;
    }
    vec
}

/* helper modified by LLM (iteration 4): fixed slice expressions in invariants */
fn bit_add(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
    requires
        valid_bit_string(a@) && valid_bit_string(b@)
    ensures
        valid_bit_string(res@),
        str2int(res@) == str2int(a@) + str2int(b@)
{
    let mut carry = 0;
    let mut result = Vec::new();
    let mut i = a.len();
    let mut j = b.len();
    while i > 0 || j > 0 || carry > 0
        invariant
            valid_bit_string(result@),
            result@.len() == (a.len() - i) + (b.len() - j) + (if carry > 0 { 1 } else { 0 }),
            str2int(result@) + str2int(a@.subrange(0, i as int)) + str2int(b@.subrange(0, j as int)) == str2int(a@) + str2int(b@)
        decreases (i as nat) + (j as nat) + (carry as nat)
    {
        let digit_a = if i > 0 {
            if a[(i-1) as usize] == '1' { 1 } else { 0 }
        } else {
            0
        };
        let digit_b = if j > 0 {
            if b[(j-1) as usize] == '1' { 1 } else { 0 }
        } else {
            0
        };
        let sum = digit_a + digit_b + carry;
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
        if i > 0 { i -= 1; }
        if j > 0 { j -= 1; }
    }
    result.reverse();
    result
}

/* helper modified by LLM (iteration 4): fixed slice expressions in invariants */
fn bit_mul(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
    requires
        valid_bit_string(a@) && valid_bit_string(b@)
    ensures
        valid_bit_string(res@),
        str2int(res@) == str2int(a@) * str2int(b@)
{
    let mut result = create_zeros(a.len() + b.len());
    let mut i = b.len();
    while i > 0
        invariant
            valid_bit_string(result@),
            str2int(result@) + str2int(a@) * str2int(b@.subrange(0, i as int)) == str2int(a@) * str2int(b@)
        decreases i as nat
    {
        if b[(i-1) as usize] == '1' {
            let mut shifted_a = a.clone();
            let shift_count = b.len() - i;
            for _ in 0..shift_count {
                shifted_a.push('0');
            }
            result = bit_add(result, shifted_a);
        }
        i -= 1;
    }
    result
}

/* helper modified by LLM (iteration 4): fixed slice expressions in invariants */
fn bit_sub(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
    requires
        valid_bit_string(a@) && valid_bit_string(b@),
        str2int(a@) >= str2int(b@)
    ensures
        valid_bit_string(res@),
        str2int(res@) == str2int(a@) - str2int(b@)
{
    let mut borrow = 0;
    let mut result = Vec::new();
    let mut i = a.len();
    let mut j = b.len();
    while i > 0 || j > 0
        invariant
            result@.len() == (a.len() - i) + (b.len() - j),
            valid_bit_string(result@),
            str2int(result@) + str2int(a@.subrange(0, i as int)) - str2int(b@.subrange(0, j as int)) - borrow == str2int(a@) - str2int(b@)
        decreases (i as nat) + (j as nat) + (borrow as nat)
    {
        let digit_a = if i > 0 {
            if a[(i-1) as usize] == '1' { 1 } else { 0 }
        } else {
            0
        };
        let digit_b = if j > 0 {
            if b[(j-1) as usize] == '1' { 1 } else { 0 }
        } else {
            0
        };
        let diff = digit_a - digit_b - borrow;
        if diff < 0 {
            result.push(if diff + 2 == 1 { '1' } else { '0' });
            borrow = 1;
        } else {
            result.push(if diff == 1 { '1' } else { '0' });
            borrow = 0;
        }
        if i > 0 { i -= 1; }
        if j > 0 { j -= 1; }
    }
    result.reverse();
    let mut first_non_zero = 0;
    while first_non_zero < result.len() && result[first_non_zero] == '0' {
        first_non_zero += 1;
    }
    if first_non_zero == result.len() {
        vec!['0']
    } else {
        result[first_non_zero..].to_vec()
    }
}

/* helper modified by LLM (iteration 4): fixed slice expressions in invariants */
fn bit_mod(a: Vec<char>, modulus: Vec<char>) -> (res: Vec<char>)
    requires
        valid_bit_string(a@) && valid_bit_string(modulus@),
        str2int(modulus@) > 1
    ensures
        valid_bit_string(res@),
        str2int(res@) == str2int(a@) % str2int(modulus@)
{
    let mut current = create_zeros(1);
    for i in 0..a.len()
        invariant
            valid_bit_string(current@),
            str2int(current@) < str2int(modulus@),
            str2int(current@) * exp_int(2, (a.len() - i) as nat) + str2int(a@.subrange(i as int, a@.len())) % str2int(modulus@) ==
            str2int(a@.subrange(i as int, a@.len())) % str2int(modulus@)
        decreases (a.len() - i) as nat
    {
        current = bit_add(current, current);
        if a[i] == '1' {
            current = bit_add(current, vec!['1']);
        }
        if current.len() > modulus.len() ||
           (current.len() == modulus.len() && current >= modulus) {
            current = bit_sub(current, modulus);
        }
    }
    current
}

fn bit_mul_mod(a: Vec<char>, b: Vec<char>, modulus: Vec<char>) -> (res: Vec<char>)
    requires
        valid_bit_string(a@) && valid_bit_string(b@) && valid_bit_string(modulus@),
        str2int(modulus@) > 1
    ensures
        valid_bit_string(res@),
        str2int(res@) == (str2int(a@) * str2int(b@)) % str2int(modulus@)
{
    let product = bit_mul(a, b);
    bit_mod(product, modulus)
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy@.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): no changes needed */
    if sy.len() == 1 {
        if sy[0] == '1' {
            bit_mod(sx, sz)
        } else {
            vec!['1']
        }
    } else {
        let sy_high = sy[0..sy.len()-1].to_vec();
        let sy_low = sy[sy.len()-1];
        let t = mod_exp(sx, sy_high, sz);
        let t_sq = bit_mul(t, t);
        let t_sq_mod = bit_mod(t_sq, sz);
        if sy_low == '1' {
            bit_mul_mod(t_sq_mod, sx, sz)
        } else {
            t_sq_mod
        }
    }
}
// </vc-code>


}

fn main() {}