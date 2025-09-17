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
/* helper modified by LLM (iteration 8): fixed integer literal types in decreases clause */
spec fn pow2(n: nat) -> nat
decrases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn lemma_str2int_append_bit(s: Seq<char>, bit: char)
    requires ValidBitString(s), bit == '0' || bit == '1'
    ensures ValidBitString(s.push(bit)),
        Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat })
{
}

proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_valid_empty()
    ensures ValidBitString(Seq::<char>::empty())
{
}

exec fn add_bit_strings(s1: &[char], s2: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s1@), ValidBitString(s2@)
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
{
    let mut result = Vec::<char>::new();
    let mut carry = false;
    let mut i = 0;
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry
        invariant
            ValidBitString(result@),
            i <= max_len + 1,
        decreases (max_len + 1) - i + (if carry { 1int } else { 0int })
    {
        let bit1 = if i < s1.len() && s1.len() > i { s1[s1.len() - 1 - i] == '1' } else { false };
        let bit2 = if i < s2.len() && s2.len() > i { s2[s2.len() - 1 - i] == '1' } else { false };
        
        let sum = (if bit1 { 1 } else { 0 }) + (if bit2 { 1 } else { 0 }) + (if carry { 1 } else { 0 });
        
        if sum % 2 == 1 {
            result.insert(0, '1');
        } else {
            result.insert(0, '0');
        }
        
        carry = sum >= 2;
        i += 1;
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 8): no changes needed from previous iteration */
    if s1.len() == 0 || s2.len() == 0 {
        return vec!['0'];
    }
    
    let mut result = vec!['0'];
    
    for i in 0..s1.len()
        invariant ValidBitString(result@)
    {
        if s1[s1.len() - 1 - i] == '1' {
            let mut shifted_s2 = Vec::<char>::new();
            for j in 0..s2.len() {
                shifted_s2.push(s2[j]);
            }
            for _ in 0..i {
                shifted_s2.push('0');
            }
            result = add_bit_strings(&result, &shifted_s2);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}
