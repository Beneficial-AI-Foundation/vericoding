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
/* helper modified by LLM (iteration 9): Added helper to convert u64 to bit string and prove properties */
proof fn lemma_str2int_append(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        Str2Int(s.push(c)) == 2 * Str2Int(s) + if c == '1' { 1nat } else { 0nat },
    decreases s.len()
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
    let empty: Seq<char> = seq![];
    assert(seq!['0'].subrange(0, 0) == empty);
    assert(Str2Int(seq![]) == 0);
    assert(seq!['0'].index(0) == '0');
}

proof fn lemma_str2int_properties(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
    ensures
        Str2Int(s) >= 0,
    decreases s.len()
{
    if s.len() == 1 {
        if s.index(0) == '0' {
            lemma_str2int_zero();
        }
    } else {
        lemma_str2int_properties(s.subrange(0, s.len() as int - 1));
    }
}

spec fn U64ToBitString(val: u64) -> Seq<char>
    decreases val
{
    if val == 0 {
        seq!['0']
    } else {
        let bit = if val % 2 == 1 { '1' } else { '0' };
        U64ToBitString(val / 2).push(bit)
    }
}

proof fn lemma_u64_to_bitstring_valid(val: u64)
    ensures
        ValidBitString(U64ToBitString(val)),
        Str2Int(U64ToBitString(val)) == val,
    decreases val
{
    if val == 0 {
        lemma_str2int_zero();
    } else {
        lemma_u64_to_bitstring_valid(val / 2);
        let bit = if val % 2 == 1 { '1' } else { '0' };
        lemma_str2int_append(U64ToBitString(val / 2), bit);
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
    /* code modified by LLM (iteration 9): Fixed overflow issues and invariant establishment */
    let mut quotient = Vec::<char>::new();
    let mut remainder_val: u64 = 0;
    let ghost mut ghost_remainder_val: nat = 0nat;
    let ghost divisor_val = Str2Int(divisor@);
    
    let exec_divisor_val: u64 = {
        let mut val: u64 = 0;
        let mut idx = 0;
        while idx < divisor.len()
            invariant
                0 <= idx <= divisor.len(),
                ValidBitString(divisor@.subrange(0, idx as int)),
                val as nat == Str2Int(divisor@.subrange(0, idx as int)),
                val <= u64::MAX / 2,
            decreases divisor.len() - idx
        {
            let old_val = val;
            val = val.checked_mul(2).expect("overflow");
            val = val.checked_add(if divisor[idx] == '1' { 1 } else { 0 }).expect("overflow");
            idx = idx + 1;
        }
        val
    };
    
    proof {
        assert(exec_divisor_val as nat == Str2Int(divisor@));
        assert(exec_divisor_val as nat == divisor_val);
    }
    
    let mut i = 0;
    while i < dividend.len()
        invariant
            0 <= i <= dividend.len(),
            ValidBitString(quotient@),
            ghost_remainder_val < divisor_val,
            remainder_val as nat == ghost_remainder_val,
            exec_divisor_val as nat == divisor_val,
            i > 0 ==> Str2Int(quotient@) * divisor_val + ghost_remainder_val == Str2Int(dividend@.subrange(0, i as int)),
            i == 0 ==> quotient.len() == 0 && ghost_remainder_val == 0nat,
            remainder_val <= u64::MAX / 2,
        decreases dividend.len() - i
    {
        let bit = dividend[i];
        let old_remainder = remainder_val;
        remainder_val = remainder_val.checked_mul(2).expect("overflow");
        remainder_val = remainder_val.checked_add(if bit == '1' { 1 } else { 0 }).expect("overflow");
        proof {
            ghost_remainder_val = ghost_remainder_val * 2 + if bit == '1' { 1nat } else { 0nat };
        }
        
        if remainder_val >= exec_divisor_val {
            quotient.push('1');
            remainder_val = remainder_val - exec_divisor_val;
            proof {
                assert(ghost_remainder_val >= divisor_val);
                ghost_remainder_val = (ghost_remainder_val - divisor_val) as nat;
            }
        } else {
            quotient.push('0');
        }
        
        proof {
            if i > 0 {
                lemma_str2int_append(dividend@.subrange(0, i as int), bit);
            }
            if quotient.len() > 0 {
                lemma_str2int_append(quotient@.subrange(0, quotient.len() as int - 1), quotient[quotient.len() - 1]);
            }
        }
        
        i = i + 1;
    }
    
    let remainder = if remainder_val == 0 {
        let mut r = Vec::<char>::new();
        r.push('0');
        r
    } else {
        let ghost remainder_seq = U64ToBitString(remainder_val);
        proof {
            lemma_u64_to_bitstring_valid(remainder_val);
            assert(ValidBitString(remainder_seq));
            assert(Str2Int(remainder_seq) == remainder_val);
        }
        
        let mut r = Vec::<char>::new();
        let mut temp = remainder_val;
        let mut bits = Vec::<char>::new();
        
        while temp > 0
            invariant
                temp >= 0,
                ValidBitString(bits@),
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
                ValidBitString(r@),
            decreases j
        {
            j = j - 1;
            r.push(bits[j]);
        }
        r
    };
    
    proof {
        assert(Str2Int(quotient@) * divisor_val + ghost_remainder_val == Str2Int(dividend@));
        assert(Str2Int(remainder@) == ghost_remainder_val);
        assert(Str2Int(quotient@) == Str2Int(dividend@) / Str2Int(divisor@));
        assert(Str2Int(remainder@) == Str2Int(dividend@) % Str2Int(divisor@));
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

