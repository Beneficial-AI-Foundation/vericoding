use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed compilation errors by using slice indexing instead of ghost indexing */
exec fn is_ge(a: &[char], b: &[char]) -> (res: bool)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures res == (Str2Int(a@) >= Str2Int(b@))
{
    let mut a_start: usize = a.len();
    let mut i: usize = 0;
    while i < a.len()
        invariant 
            i <= a.len(),
    {
        if a[i] == '1' {
            a_start = i;
            break;
        }
        i = i + 1;
    }
    let a_eff_len = a.len() - a_start;

    let mut b_start: usize = b.len();
    i = 0;
    while i < b.len()
        invariant 
            i <= b.len(),
    {
        if b[i] == '1' {
            b_start = i;
            break;
        }
        i = i + 1;
    }
    let b_eff_len = b.len() - b_start;
    
    if a_eff_len != b_eff_len {
        return a_eff_len > b_eff_len;
    }

    if a_eff_len == 0 { return true; }

    i = 0;
    while i < a_eff_len
        invariant 
            i <= a_eff_len,
    {
        let a_idx = a_start + i;
        let b_idx = b_start + i;
        if a[a_idx] != b[b_idx] {
            return a[a_idx] == '1';
        }
        i = i + 1;
    }
    
    true
}

/* helper modified by LLM (iteration 4): fixed compilation errors by using slice indexing instead of ghost indexing */
exec fn add_one(v_slice: &[char]) -> (res: Vec<char>)
    requires ValidBitString(v_slice@)
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(v_slice@) + 1
{
    let mut result = v_slice.to_vec();
    let mut i: usize = result.len();
    while i > 0
        invariant 
            i <= result.len(),
    {
        i = i - 1;
        if result[i] == '0' {
            result.set(i, '1');
            return result;
        }
        result.set(i, '0');
    }
    
    let mut new_vec = vec!['1'];
    new_vec.append(&mut result);
    new_vec
}

/* helper modified by LLM (iteration 5): fixed compile error by using subslice().to_vec() */
exec fn subtract(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(a@),
        ValidBitString(b@),
        Str2Int(a@) >= Str2Int(b@)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(a@) - Str2Int(b@)
{
    let mut res = a.to_vec();
    let len_a = a.len();
    let len_b = b.len();
    
    let mut borrow = false;
    let mut i: usize = 1;
    while i <= len_a
        invariant
            1 <= i <= len_a + 1,
    {
        let a_idx = len_a - i;
        let a_bit = a[a_idx];
        let b_bit = if i <= len_b { b[len_b - i] } else { '0' };
        
        let a_val = if a_bit == '1' { 1 } else { 0 };
        let b_val = if b_bit == '1' { 1 } else { 0 };
        let borrow_val = if borrow { 1 } else { 0 };

        let mut diff = a_val - borrow_val - b_val;
        if diff < 0 {
            diff = diff + 2;
            borrow = true;
        } else {
            borrow = false;
        }
        
        res.set(a_idx, if diff == 1 { '1' } else { '0' });
        i = i + 1;
    }
    
    let mut first_one = res.len();
    let mut j: usize = 0;
    while j < res.len()
        invariant
            j <= res.len(),
    {
        if res[j] == '1' {
            first_one = j;
            break;
        }
        j = j + 1;
    }

    if first_one == res.len() {
        vec!['0']
    } else {
        res.as_slice().subslice(first_one as int, res.len() as int).to_vec()
    }
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes required, fixed compilation error in helper */
    let mut remainder = dividend.to_vec();
    let mut quotient = vec!['0'];

    let ghost spec_dividend_val = Str2Int(dividend@);
    let ghost spec_divisor_val = Str2Int(divisor@);

    while is_ge(remainder.as_slice(), divisor)
        invariant
            ValidBitString(remainder@),
            ValidBitString(quotient@),
            ValidBitString(divisor@),
            spec_divisor_val > 0,
            spec_dividend_val == Str2Int(quotient@) * spec_divisor_val + Str2Int(remainder@),
        decreases Str2Int(remainder@)
    {
        let ghost old_remainder_val = Str2Int(remainder@);
        
        remainder = subtract(remainder.as_slice(), divisor);
        quotient = add_one(quotient.as_slice());
        
        assert(Str2Int(remainder@) < old_remainder_val) by {
            assert(Str2Int(remainder@) == old_remainder_val - spec_divisor_val);
            assert(spec_divisor_val > 0);
        }
    }

    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

