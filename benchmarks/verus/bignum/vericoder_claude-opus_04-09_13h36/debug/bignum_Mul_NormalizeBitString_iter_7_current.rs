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
// Helper function to convert a sequence of binary chars to nat
exec fn str_to_nat(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
    decreases s.len()
{
    if s.len() == 0 {
        return 0;
    }
    
    let n = s.len();
    let last = s[n - 1];
    let rest = &s[..n-1];
    
    let rest_val = str_to_nat(rest);
    let last_val = if last == '1' { 1nat } else { 0nat };
    
    proof {
        assert(s@.subrange(0, (n-1) as int) == rest@);
        assert(s@.index((n-1) as int) == last);
    }
    
    2 * rest_val + last_val
}

// Helper function to convert nat to binary string
exec fn nat_to_str(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == n
    ensures res@.len() >= 1
{
    if n == 0 {
        let mut res = Vec::new();
        res.push('0');
        proof {
            assert(res@.len() == 1);
            assert(res@.index(0) == '0');
            assert(ValidBitString(res@));
            assert(Str2Int(res@) == 2 * Str2Int(res@.subrange(0, 0)) + 0);
            assert(res@.subrange(0, 0).len() == 0);
            assert(Str2Int(res@.subrange(0, 0)) == 0);
            assert(Str2Int(res@) == 0);
        }
        return res;
    }
    
    let mut result = Vec::new();
    let mut temp = n;
    
    // Build the binary string directly in correct order
    let mut power: nat = 1;
    let mut bits = Vec::new();
    
    // Find highest bit position
    while power * 2 <= n
        invariant power >= 1
    {
        power = power * 2;
    }
    
    // Build string from highest bit to lowest
    while power > 0
        invariant 
            temp <= n,
            ValidBitString(result@),
            power >= 1 ==> temp < power * 2
    {
        if temp >= power {
            result.push('1');
            temp = temp - power;
        } else {
            result.push('0');
        }
        if power > 1 {
            power = power / 2;
        } else {
            power = 0;
        }
    }
    
    // Handle edge case where n was 0 (shouldn't happen due to early return)
    if result.len() == 0 {
        result.push('0');
    }
    
    proof {
        assert(ValidBitString(result@));
        assert(result@.len() >= 1);
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = str_to_nat(s1);
    let n2 = str_to_nat(s2);
    let product = n1 * n2;
    
    let res = nat_to_str(product);
    
    proof {
        assert(n1 == Str2Int(s1@));
        assert(n2 == Str2Int(s2@));
        assert(product == n1 * n2);
        assert(Str2Int(res@) == product);
        assert(Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@));
    }
    
    res
}
// </vc-code>

fn main() {}
}