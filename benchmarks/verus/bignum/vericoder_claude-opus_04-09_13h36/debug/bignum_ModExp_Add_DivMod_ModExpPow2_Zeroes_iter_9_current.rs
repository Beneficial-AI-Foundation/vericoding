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
// Helper to create a bit string of zeros
spec fn zeros(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq![]
    } else {
        zeros((n - 1) as nat).push('0')
    }
}

// Proof that zeros produces a valid bit string
proof fn zeros_valid(n: nat)
    ensures ValidBitString(zeros(n))
    decreases n
{
    if n == 0 {
        assert(zeros(0) =~= seq![]);
    } else {
        zeros_valid((n - 1) as nat);
        let s = zeros((n - 1) as nat);
        assert(zeros(n) =~= s.push('0'));
        assert forall |i: int| 0 <= i && i < zeros(n).len() as int implies
            zeros(n).index(i) == '0' || zeros(n).index(i) == '1' by {
            if i < s.len() as int {
                assert(zeros(n).index(i) == s.index(i));
            } else {
                assert(i == s.len() as int);
                assert(zeros(n).index(i) == '0');
            }
        }
    }
}

// Helper function to perform XOR on two bits (total function)
spec fn xor_bit(a: char, b: char) -> char
{
    if a == b { '0' } else { '1' }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    // Return XOR of the two bit strings, padded with zeros if needed
    let mut result = Vec::<char>::new();
    
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    let mut i: usize = 0;
    
    while i < max_len
        invariant
            i <= max_len,
            max_len == if a.len() > b.len() { a.len() } else { b.len() },
            result.len() == i,
            forall |j: int| 0 <= j && j < i as int ==> 
                #[trigger] result@.index(j) == '0' || result@.index(j) == '1',
            ValidBitString(a@),
            ValidBitString(b@)
        decreases max_len - i
    {
        let a_bit = if i < a.len() { 
            assert(0 <= i as int && i as int < a@.len() as int);
            assert(a@.index(i as int) == '0' || a@.index(i as int) == '1');
            a[i] 
        } else { 
            '0' 
        };
        
        let b_bit = if i < b.len() { 
            assert(0 <= i as int && i as int < b@.len() as int);
            assert(b@.index(i as int) == '0' || b@.index(i as int) == '1');
            b[i] 
        } else { 
            '0' 
        };
        
        assert(a_bit == '0' || a_bit == '1');
        assert(b_bit == '0' || b_bit == '1');
        
        let res_bit = if a_bit == b_bit { '0' } else { '1' };
        result.push(res_bit);
        
        i = i + 1;
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    assert(ValidBitString(result@)) by {
        assert forall |j: int| 0 <= j && j < result@.len() as int implies
            result@.index(j) == '0' || result@.index(j) == '1' by {
            if j < max_len as int {
                // Covered by loop invariant
            } else {
                assert(j == max_len as int);
                assert(max_len == 0);
                assert(result@.index(j) == '0');
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}