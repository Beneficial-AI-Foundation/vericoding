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
proof fn lemma_str2int_append(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        Str2Int(s.push(c)) == 2 * Str2Int(s) + if c == '1' { 1nat } else { 0nat },
{
    let s_new = s.push(c);
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
    assert(s_new.index(s_new.len() as int - 1) == c);
}

proof fn lemma_str2int_zero()
    ensures
        Str2Int(seq!['0']) == 0,
{
    assert(seq!['0'].len() == 1);
    /* helper modified by LLM (iteration 2): fixed type inference for empty sequence */
    assert(seq!['0'].subrange(0, 0) =~= Seq::<char>::empty());
    assert(seq!['0'].index(0) == '0');
}

proof fn lemma_str2int_bounds(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
    ensures
        Str2Int(s) < pow2(s.len()),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(pow2(1) == 2);
        if s.index(0) == '0' {
            assert(Str2Int(s) == 0);
        } else {
            assert(Str2Int(s) == 1);
        }
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        lemma_str2int_bounds(prefix);
        assert(Str2Int(prefix) < pow2(prefix.len()));
        assert(pow2(s.len()) == 2 * pow2(prefix.len()));
    }
}

/* helper modified by LLM (iteration 2): fixed nat type for pow2 parameter */
spec fn pow2(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

exec fn compare_binary(a: &[char], b: &[char]) -> (res: bool)
    requires
        ValidBitString(a@),
        ValidBitString(b@),
    ensures
        res == (Str2Int(a@) >= Str2Int(b@)),
{
    if a.len() > b.len() {
        return true;
    } else if a.len() < b.len() {
        return false;
    } else {
        let mut i = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                forall |j: int| 0 <= j && j < i ==> a@.index(j) == b@.index(j),
        {
            if a[i] == '1' && b[i] == '0' {
                return true;
            } else if a[i] == '0' && b[i] == '1' {
                return false;
            }
            i = i + 1;
        }
        return true;
    }
}

exec fn subtract_binary(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(a@),
        ValidBitString(b@),
        Str2Int(a@) >= Str2Int(b@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(a@) - Str2Int(b@),
{
    let mut result = Vec::new();
    let mut borrow = 0u8;
    let mut i = 0;
    
    while i < a.len() || i < b.len() || borrow > 0
        invariant
            0 <= i <= a.len() + b.len(),
            borrow == 0 || borrow == 1,
            ValidBitString(result@),
    {
        let a_bit = if i < a.len() {
            if a[a.len() - 1 - i] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let b_bit = if i < b.len() {
            if b[b.len() - 1 - i] == '1' { 1u8 } else { 0u8 }
        } else { 0u8 };
        
        let diff = (a_bit + 2) - b_bit - borrow;
        if diff >= 2 {
            result.push('1');
            borrow = 0;
        } else if diff == 1 {
            result.push('1');
            borrow = 0;
        } else if diff == 0 {
            result.push('0');
            borrow = 1;
        } else {
            result.push('1');
            borrow = 1;
        }
        i = i + 1;
    }
    
    result.reverse();
    
    while result.len() > 1 && result[0] == '0'
        invariant
            ValidBitString(result@),
            result.len() >= 1,
    {
        result.remove(0);
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
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
    /* code modified by LLM (iteration 2): keeping implementation simple */
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    for i in 0..dividend.len() {
        remainder.push(dividend[i]);
        
        while remainder.len() > 1 && remainder[0] == '0' {
            remainder.remove(0);
        }
        
        if compare_binary(&remainder, divisor) {
            quotient.push('1');
            remainder = subtract_binary(&remainder, divisor);
        } else {
            quotient.push('0');
        }
    }
    
    while quotient.len() > 1 && quotient[0] == '0' {
        quotient.remove(0);
    }
    
    if quotient.len() == 0 {
        quotient.push('0');
    }
    
    if remainder.len() == 0 {
        remainder.push('0');
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

