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
exec fn binary_string_to_nat(s: &[char]) -> (result: nat)
    requires ValidBitString(s@)
    ensures result == Str2Int(s@)
{
    let mut result: nat = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            ValidBitString(s@),
            result == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(0, s.len() as int) =~= s@);
    }
    
    result
}

exec fn nat_to_binary_string(mut n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let mut digits = Vec::new();
    let mut temp_n = n;
    
    while temp_n > 0
        invariant 
            ValidBitString(digits@),
            n == temp_n + Str2Int(digits@) * pow2(digits.len())
    {
        if temp_n % 2 == 0 {
            digits.push('0');
        } else {
            digits.push('1');
        }
        temp_n = temp_n / 2;
    }
    
    // Reverse the digits
    let mut result = Vec::new();
    let mut i = digits.len();
    
    while i > 0
        invariant 
            ValidBitString(digits@),
            ValidBitString(result@),
            i <= digits.len(),
            Str2Int(result@) + Str2Int(digits@.subrange(0, i as int)) * pow2(result.len()) == n
    {
        i = i - 1;
        result.push(digits[i]);
    }
    
    result
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = binary_string_to_nat(s1);
    let n2 = binary_string_to_nat(s2);
    let product = n1 * n2;
    let result = nat_to_binary_string(product);
    
    proof {
        assert(Str2Int(result@) == product);
        assert(product == n1 * n2);
        assert(n1 == Str2Int(s1@));
        assert(n2 == Str2Int(s2@));
        assert(Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@));
    }
    
    result
}
// </vc-code>

fn main() {}
}