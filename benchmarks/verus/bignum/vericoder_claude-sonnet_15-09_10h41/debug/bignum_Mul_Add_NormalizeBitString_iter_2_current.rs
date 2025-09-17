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
/* helper modified by LLM (iteration 2): fixed nat type errors and removed invalid nat::pow */
proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
}

proof fn lemma_str2int_single_one()
    ensures Str2Int(seq!['1']) == 1
{
}

proof fn lemma_str2int_distributive(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2)
    ensures Str2Int(s1 + s2) == Str2Int(s1) * pow(2nat, s2.len() as nat) + Str2Int(s2)
    decreases s1.len()
{
}

proof fn lemma_multiplication_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) * 0 == 0
{
}

exec fn nat_to_bit_string(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    if n == 0nat {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0nat
            invariant ValidBitString(result@)
        {
            if temp % 2nat == 0nat {
                result.insert(0, '0');
            } else {
                result.insert(0, '1');
            }
            temp = temp / 2nat;
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed nat type errors */
    if s1.len() == 0 || s2.len() == 0 {
        return vec!['0'];
    }
    
    let val1 = Str2Int(s1@);
    let val2 = Str2Int(s2@);
    let product = val1 * val2;
    
    if product == 0nat {
        return vec!['0'];
    }
    
    let mut result = Vec::new();
    let mut temp = product;
    
    while temp > 0nat
        invariant
            ValidBitString(result@),
            temp * pow(2nat, result@.len() as nat) + Str2Int(result@) == product
    {
        if temp % 2nat == 0nat {
            result.insert(0, '0');
        } else {
            result.insert(0, '1');
        }
        temp = temp / 2nat;
    }
    
    proof {
        lemma_str2int_distributive(s1@, s2@);
        lemma_multiplication_zero(s1@);
    }
    
    result
}
// </vc-code>

fn main() {}
}
