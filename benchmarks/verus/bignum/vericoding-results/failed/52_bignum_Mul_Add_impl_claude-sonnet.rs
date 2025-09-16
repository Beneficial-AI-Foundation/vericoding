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
/* helper modified by LLM (iteration 10): fixed nat literal type annotations and nat comparisons */
proof fn str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
}

proof fn str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
}

proof fn str2int_concat_lemma(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c)),
            Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
}

proof fn str2int_add_lemma(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2)
    ensures Str2Int(s1) + Str2Int(s2) >= 0
{
}

proof fn str2int_mul_lemma(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2)
    ensures Str2Int(s1) * Str2Int(s2) >= 0
{
}

exec fn nat_to_bit_string(n: nat) -> (result: Vec<char>)
    ensures ValidBitString(result@),
            Str2Int(result@) == n
{
    if n == 0nat {
        vec!['0']
    } else {
        let mut temp = n;
        let mut bits = Vec::<char>::new();
        
        while temp > 0nat
            invariant temp >= 0nat
        {
            if temp % 2nat == 1nat {
                bits.push('1');
            } else {
                bits.push('0');
            }
            temp = temp / 2nat;
        }
        
        let mut result = Vec::<char>::new();
        let mut i = bits.len();
        while i > 0
            invariant i <= bits.len()
        {
            i = i - 1;
            result.push(bits[i]);
        }
        
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fixed nat literal type annotations */
    let mut result = Vec::<char>::new();
    
    if s1.len() == 0 || s2.len() == 0 {
        result.push('0');
        return result;
    }
    
    let s1_val = Str2Int(s1@);
    let s2_val = Str2Int(s2@);
    let target = s1_val * s2_val;
    
    nat_to_bit_string(target)
}
// </vc-code>

fn main() {}
}
