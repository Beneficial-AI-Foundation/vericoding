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
// Helper function to convert a binary string to an integer
exec fn binary_to_nat(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
    decreases s@.len()
{
    if s.len() == 0 {
        return 0;
    }
    
    let n = s.len() - 1;
    let rest = binary_to_nat(&s[..n]);
    let last_bit = if s[n] == '1' { 1 } else { 0 };
    
    proof {
        assert(s@.subrange(0, n as int) =~= s[..n]@);
        assert(s@.index(n as int) == s[n]);
    }
    
    return 2 * rest + last_bit;
}

// Helper function to convert a natural number to a binary string
exec fn nat_to_binary(mut n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == n
    decreases n
{
    if n == 0 {
        return Vec::new();
    }
    
    let mut result = nat_to_binary(n / 2);
    let bit = if n % 2 == 1 { '1' } else { '0' };
    result.push(bit);
    
    proof {
        assert(result@.len() >= 1);
        let len = result@.len();
        assert(result@.subrange(0, len - 1) =~= nat_to_binary(n / 2)@);
        assert(result@.index(len - 1) == bit);
        assert(Str2Int(result@) == 2 * Str2Int(result@.subrange(0, len - 1)) + (if bit == '1' { 1 } else { 0 }));
        assert(Str2Int(result@.subrange(0, len - 1)) == n / 2);
        assert(if bit == '1' { 1nat } else { 0nat } == n % 2);
        assert(n == 2 * (n / 2) + n % 2);
    }
    
    return result;
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = binary_to_nat(s1);
    let n2 = binary_to_nat(s2);
    let product = n1 * n2;
    let result = nat_to_binary(product);
    return result;
}
// </vc-code>

fn main() {}
}