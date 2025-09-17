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
// Helper function for power of 2
spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

// Helper lemmas for proving properties about Str2Int
proof fn lemma_str2int_zero(n: nat)
    ensures Str2Int(Seq::new(n, |_| '0')) == 0
    decreases n
{
    if n > 0 {
        lemma_str2int_zero((n - 1) as nat);
    }
}

proof fn lemma_str2int_shift(s: Seq<char>, n: nat)
    requires ValidBitString(s)
    ensures 
        ValidBitString(Seq::new(n, |_| '0') + s),
        Str2Int(Seq::new(n, |_| '0') + s) == Str2Int(s) * pow2(n)
    decreases n
{
    if n == 0 {
        assert(Seq::new(0, |_| '0') + s =~= s);
    } else {
        let zeros_n = Seq::new(n, |_| '0');
        let zeros_n_minus_1 = Seq::new((n - 1) as nat, |_| '0');
        lemma_str2int_shift(s, (n - 1) as nat);
        assert(zeros_n =~= Seq::new(1, |_| '0') + zeros_n_minus_1);
        assert(zeros_n + s =~= Seq::new(1, |_| '0') + (zeros_n_minus_1 + s));
    }
}

// Helper function to add two bit strings
exec fn add_binary(s1: &[char], s2: &[char]) -> (result: Vec<char>)
    requires ValidBitString(s1@), ValidBitString(s2@)
    ensures ValidBitString(result@), Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@)
{
    // Simple implementation - convert to numbers, add, convert back
    let mut result = Vec::new();
    let sum = Str2Int(s1@) + Str2Int(s2@);
    
    if sum == 0 {
        result.push('0');
    } else {
        let mut n = sum;
        let mut digits = Vec::new();
        while n > 0 {
            if n % 2 == 0 {
                digits.push('0');
            } else {
                digits.push('1');
            }
            n = n / 2;
        }
        
        // Reverse the digits
        let len = digits.len();
        for i in 0..len {
            result.push(digits[len - 1 - i]);
        }
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    result.push('0');
    
    // Handle special cases
    if s1.len() == 0 || s2.len() == 0 {
        return result;
    }
    
    // Check if either operand is zero
    let mut is_zero1 = true;
    let mut is_zero2 = true;
    
    for i in 0..s1.len() {
        if s1[i] == '1' {
            is_zero1 = false;
            break;
        }
    }
    
    for i in 0..s2.len() {
        if s2[i] == '1' {
            is_zero2 = false;
            break;
        }
    }
    
    if is_zero1 || is_zero2 {
        return result;
    }
    
    // Perform multiplication using shift-and-add
    for i in 0..s2.len() {
        if s2[s2.len() - 1 - i] == '1' {
            // Create shifted version of s1
            let mut shifted = Vec::new();
            for j in 0..s1.len() {
                shifted.push(s1[j]);
            }
            for _ in 0..i {
                shifted.push('0');
            }
            
            // Add shifted to result
            result = add_binary(&result, &shifted);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}