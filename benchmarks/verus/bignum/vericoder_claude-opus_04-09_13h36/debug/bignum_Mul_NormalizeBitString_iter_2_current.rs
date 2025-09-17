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
exec fn nat_to_str(mut n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == n
    decreases n
{
    if n == 0 {
        let mut res = Vec::new();
        res.push('0');
        proof {
            assert(res@.len() == 1);
            assert(res@.index(0) == '0');
            assert(ValidBitString(res@));
            // Prove Str2Int for single '0'
            assert(Str2Int(res@) == 2 * Str2Int(res@.subrange(0, 0)) + 0);
            assert(res@.subrange(0, 0).len() == 0);
            assert(Str2Int(res@.subrange(0, 0)) == 0);
            assert(Str2Int(res@) == 0);
        }
        return res;
    }
    
    let mut res = nat_to_str(n / 2);
    let digit = if n % 2 == 1 { '1' } else { '0' };
    res.push(digit);
    
    proof {
        let old_res = res@.subrange(0, res@.len() as int - 1);
        assert(ValidBitString(old_res));
        assert(res@.index(res@.len() as int - 1) == digit);
        assert(n % 2 == if digit == '1' { 1 } else { 0 });
        
        // Prove that Str2Int(res@) == n
        assert(Str2Int(res@) == 
            2 * Str2Int(res@.subrange(0, res@.len() as int - 1)) + 
            (if res@.index(res@.len() as int - 1) == '1' { 1nat } else { 0nat }));
        assert(old_res == res@.subrange(0, res@.len() as int - 1));
        assert(Str2Int(old_res) == n / 2);
        assert(Str2Int(res@) == 2 * (n / 2) + (n % 2));
        assert(n == 2 * (n / 2) + (n % 2));
    }
    
    res
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