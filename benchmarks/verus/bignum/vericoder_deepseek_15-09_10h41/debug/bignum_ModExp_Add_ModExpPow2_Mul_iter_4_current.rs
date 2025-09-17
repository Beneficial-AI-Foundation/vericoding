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
/* helper modified by LLM (iteration 4): Adding missing helper lemmas for string to int conversion */
proof fn lemma_str2int_zero_append(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s + seq!['0']) == 2 * Str2Int(s)
{
    if s.len() > 0 {
        let base = s.subrange(0, s.len() as int - 1);
        let last = s.index(s.len() as int - 1);
        if last == '0' {
            assert(Str2Int(s) == 2 * Str2Int(base) + 0);
            assert(2 * Str2Int(s) == 4 * Str2Int(base));
        } else {
            assert(Str2Int(s) == 2 * Str2Int(base) + 1);
            assert(2 * Str2Int(s) == 4 * Str2Int(base) + 2);
        }
    }
    assert(Str2Int(s + seq!['0']) == 2 * Str2Int(s) + 0);
}

proof fn lemma_str2int_one_append(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s + seq!['1']) == 2 * Str2Int(s) + 1
{
    if s.len() > 0 {
        let base = s.subrange(0, s.len() as int - 1);
        let last = s.index(s.len() as int - 1);
        if last == '0' {
            assert(Str2Int(s) == 2 * Str2Int(base) + 0);
            assert(2 * Str2Int(s) + 1 == 4 * Str2Int(base) + 1);
        } else {
            assert(Str2Int(s) == 2 * Str2Int(base) + 1);
            assert(2 * Str2Int(s) + 1 == 4 * Str2Int(base) + 3);
        }
    }
    assert(Str2Int(s + seq!['1']) == 2 * Str2Int(s) + 1);
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Implement proper binary addition logic */
{
    let mut res = Vec::<char>::new();
    let mut i = a.len() - 1;
    let mut j = b.len() - 1;
    let mut carry = 0;
    
    while i >= 0 || j >= 0 || carry > 0
    {
        let mut sum = carry;
        if i >= 0 {
            sum += if a[i] == '1' { 1 } else { 0 };
            i -= 1;
        }
        if j >= 0 {
            sum += if b[j] == '1' { 1 } else { 0 };
            j -= 1;
        }
        
        res.push(if sum % 2 == 0 { '0' } else { '1' });
        carry = sum / 2;
    }
    
    res.reverse();
    res
}
// </vc-code>

fn main() {}
}

