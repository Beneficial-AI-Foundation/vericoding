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
exec fn int_to_bit_string(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    if n == 0nat {
        let mut result = Vec::new();
        result.push('0');
        assert(result@ == seq!['0']);
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == 0nat);
        result
    } else {
        let mut result = Vec::new();
        let mut val = n;
        
        while val > 0nat
            invariant ValidBitString(result@),
                     val >= 0nat,
                     Str2Int(result@) + val * nat_pow(2nat, result.len() as nat) == n
        {
            if val % 2nat == 0nat {
                result.push('0');
            } else {
                result.push('1');
            }
            val = val / 2nat;
        }
        
        // Reverse to get correct bit order
        result.reverse();
        
        proof {
            assert(ValidBitString(result@));
            assert(Str2Int(result@) == n);
        }
        
        result
    }
}

exec fn bit_string_to_int(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    let mut result: nat = 0nat;
    let mut i = 0;
    
    while i < s.len()
        invariant 0 <= i <= s.len(),
                 ValidBitString(s@),
                 result == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2nat;
        if s[i] == '1' {
            result = result + 1nat;
        }
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(0, s.len() as int) =~= s@);
    }
    
    result
}

spec fn nat_pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * nat_pow(base, (exp - 1) as nat)
    }
}

proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_zero()
    ensures Str2Int(seq!['0']) == 0
{
}

proof fn lemma_multiplication_correctness(n1: nat, n2: nat)
    ensures n1 * n2 == n2 * n1
{
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let val1 = bit_string_to_int(s1);
    let val2 = bit_string_to_int(s2);
    let product = val1 * val2;
    let result = int_to_bit_string(product);
    
    proof {
        assert(val1 == Str2Int(s1@));
        assert(val2 == Str2Int(s2@));
        assert(product == val1 * val2);
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == product);
        assert(Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@));
    }
    
    result
}
// </vc-code>

fn main() {}
}