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
exec fn max_len(a: usize, b: usize) -> (res: usize)
    ensures res == if a >= b { a } else { b }
{
    if a >= b { a } else { b }
}

exec fn get_bit_at(s: &[char], i: usize) -> (bit: char)
    requires 
        ValidBitString(s@),
        i < s.len(),
    ensures 
        bit == s@[i as int],
        bit == '0' || bit == '1',
{
    s[i]
}

exec fn xor_bits(a: char, b: char) -> (res: char)
    requires
        a == '0' || a == '1',
        b == '0' || b == '1',
    ensures
        res == '0' || res == '1',
{
    if a == b { '0' } else { '1' }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let alen = a.len();
    let blen = b.len();
    let max_length = max_len(alen, blen);
    
    let mut result = Vec::<char>::new();
    let mut i: usize = 0;
    
    while i < max_length
        invariant
            i <= max_length,
            max_length == if alen >= blen { alen } else { blen },
            ValidBitString(result@),
            result@.len() == i as int,
        decreases max_length - i
    {
        let a_bit: char = if i < alen {
            get_bit_at(a, i)
        } else {
            '0'
        };
        
        let b_bit: char = if i < blen {
            get_bit_at(b, i)
        } else {
            '0'
        };
        
        let res_bit = xor_bits(a_bit, b_bit);
        result.push(res_bit);
        
        assert(result@.len() == (i + 1) as int);
        assert(forall |j: int| 0 <= j && j < result@.len() ==> 
            result@[j] == '0' || result@[j] == '1');
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}