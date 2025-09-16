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
/* helper modified by LLM (iteration 10): Fixed ValidBitString invariants and proofs */
proof fn lemma_str2int_append(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c)),
        Str2Int(s.push(c)) == 2 * Str2Int(s) + if c == '1' { 1nat } else { 0nat },
    decreases s.len()
{
    let s_new = s.push(c);
    assert forall |i: int| 0 <= i && i < s_new.len() as int implies
        s_new.index(i) == '0' || s_new.index(i) == '1'
    by {
        if i < s.len() as int {
            assert(s_new.index(i) == s.index(i));
        } else {
            assert(i == s.len() as int);
            assert(s_new.index(i) == c);
        }
    }
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) == s);
    assert(s_new.index(s_new.len() as int - 1) == c);
}

proof fn lemma_str2int_zero()
    ensures
        Str2Int(seq!['0']) == 0,
{
    assert(seq!['0'].len() == 1);
    let empty: Seq<char> = seq![];
    assert(seq!['0'].subrange(0, 0) == empty);
    assert(Str2Int(seq![]) == 0);
    assert(seq!['0'].index(0) == '0');
}

proof fn lemma_divisor_subrange(divisor: Seq<char>, idx: int)
    requires
        0 <= idx < divisor.len() as int,
        ValidBitString(divisor),
    ensures
        ValidBitString(divisor.subrange(0, idx + 1)),
{
    assert forall |i: int| 0 <= i && i < idx + 1 implies
        divisor.subrange(0, idx + 1).index(i) == '0' || divisor.subrange(0, idx + 1).index(i) == '1'
    by {
        assert(divisor.subrange(0, idx + 1).index(i) == divisor.index(i));
    }
}

proof fn lemma_dividend_subrange_valid(dividend: Seq<char>, i: int)
    requires
        0 < i <= dividend.len() as int,
        ValidBitString(dividend),
    ensures
        ValidBitString(dividend.subrange(0, i)),
{
    assert forall |j: int| 0 <= j && j < i implies
        dividend.subrange(0, i).index(j) == '0' || dividend.subrange(0, i).index(j) == '1'
    by {
        assert(dividend.subrange(0, i).index(j) == dividend.index(j));
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
    /* code modified by LLM (iteration 10): Fixed invariants and proofs for loops */
    let mut quotient = Vec::<char>::new();
    let mut remainder_val: u64 = 0;
    let ghost mut ghost_remainder_val: nat = 0nat;
    let ghost divisor_val = Str2Int(divisor@);
    
    let exec_divisor_val: u64 = {
        let mut val: u64 = 0;
        let mut idx = 0;
        proof {
            assert(ValidBitString(divisor@.subrange(0, 0)));
        }
        while idx < divisor.len()
            invariant
                0 <= idx <= divisor.len(),
                ValidBitString(divisor@),
                val as nat == Str2Int(divisor@.subrange(0, idx as int)),
                val <= u64::MAX / 2,
            decreases divisor.len() - idx
        {
            proof {
                lemma_divisor_subrange(divisor@, idx as int);
                lemma_str2int_append(divisor@.subrange(0, idx as int), divisor[idx]);
            }
            val = val.checked_mul(2).expect("overflow");
            val = val.checked_add(if divisor[idx] == '1' { 1 } else { 0 }).expect("overflow");
            idx = idx + 1;
        }
        proof {
            assert(divisor@.subrange(0, divisor.len() as int) == divisor@);
        }
        val
    };
    
    proof {
        assert(exec_divisor_val as nat == divisor_val);
    }
    
    let mut i = 0;
    while i < dividend.len()
        invariant
            0 <= i <= dividend.len(),
            ValidBitString(quotient@),
            ValidBitString(dividend@),
            ghost_remainder_val < divisor_val,
            remainder_val as nat == ghost_remainder_val,
            exec_divisor_val as nat == divisor_val,
            i == 0 ==> quotient.len() == 0 && ghost_remainder_val == 0nat,
            i > 0 ==> Str2Int(quotient@) * divisor_val + ghost_remainder_val == Str2Int(dividend@.subrange(0, i as int)),
            remainder_val <= u64::MAX / 2,
        decreases dividend.len() - i
    {
        let bit = dividend[i];
        remainder_val = remainder_val.checked_mul(2).expect("overflow");
        remainder_val = remainder_val.checked_add(if bit == '1' { 1 } else { 0 }).expect("overflow");
        
        proof {
            ghost_remainder_val = ghost_remainder_val * 2 + if bit == '1' { 1nat } else { 0nat };
            if i > 0 {
                lemma_dividend_subrange_valid(dividend@, i as int);
                lemma_str2int_append(dividend@.subrange(0, i as int), bit);
            }
        }
        
        if remainder_val >= exec_divisor_val {
            proof {
                lemma_str2int_append(quotient@, '1');
            }
            quotient.push('1');
            remainder_val = remainder_val - exec_divisor_val;
            proof {
                ghost_remainder_val = (ghost_remainder_val - divisor_val) as nat;
            }
        } else {
            proof {
                lemma_str2int_append(quotient@, '0');
            }
            quotient.push('0');
        }
        
        i = i + 1;
        
        proof {
            if i == 1 {
                assert(dividend@.subrange(0, 1).len() == 1);
                assert(dividend@.subrange(0, 1).index(0) == bit);
                if bit == '0' {
                    lemma_str2int_zero();
                }
            }
            lemma_dividend_subrange_valid(dividend@, i as int);
        }
    }
    
    let remainder = if remainder_val == 0 {
        let mut r = Vec::<char>::new();
        r.push('0');
        proof {
            lemma_str2int_zero();
        }
        r
    } else {
        let mut r = Vec::<char>::new();
        let mut temp = remainder_val;
        let mut bits = Vec::<char>::new();
        
        while temp > 0
            invariant
                temp >= 0,
            decreases temp
        {
            if temp % 2 == 1 {
                bits.push('1');
            } else {
                bits.push('0');
            }
            temp = temp / 2;
        }
        
        let mut j = bits.len();
        while j > 0
            invariant
                0 <= j <= bits.len(),
            decreases j
        {
            j = j - 1;
            r.push(bits[j]);
        }
        
        proof {
            assert forall |k: int| 0 <= k && k < r.len() as int implies
                r@.index(k) == '0' || r@.index(k) == '1' by {}
            assert(Str2Int(r@) == remainder_val);
        }
        r
    };
    
    proof {
        assert(dividend@.subrange(0, dividend.len() as int) == dividend@);
        assert(Str2Int(quotient@) * divisor_val + ghost_remainder_val == Str2Int(dividend@));
        assert(Str2Int(remainder@) == ghost_remainder_val);
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

