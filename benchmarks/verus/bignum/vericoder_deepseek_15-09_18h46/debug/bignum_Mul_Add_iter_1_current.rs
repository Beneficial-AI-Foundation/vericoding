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
proof fn helper_lemma_mult_add_commutative(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2)
    ensures Str2Int(s1) * Str2Int(s2) == Str2Int(s2) * Str2Int(s1)
{
}

proof fn helper_lemma_str2int_zero()
    ensures Str2Int(Seq::empty()) == 0
{
}

spec fn concat(s1: Seq<char>, s2: Seq<char>) -> Seq<char>
    requires ValidBitString(s1), ValidBitString(s2)
    ensures ValidBitString(result), Str2Int(result) == Str2Int(s1) * pow2(s2.len()) + Str2Int(s2)
{
    s1 + s2
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn helper_lemma_pow2_zero()
    ensures pow2(0) == 1
{
}

proof fn helper_lemma_pow2_succ(n: nat)
    ensures pow2(n + 1) == 2 * pow2(n)
{
}

proof fn helper_lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s + Seq::new().push('0')) == 2 * Str2Int(s)
{
}

proof fn helper_lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s + Seq::new().push('1')) == 2 * Str2Int(s) + 1
{
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    let mut temp_s1 = s1.to_vec();
    let mut temp_s2 = s2.to_vec();
    
    while !temp_s2.is_empty()
        invariant
            ValidBitString(result@),
            ValidBitString(temp_s2@),
            Str2Int(result@) * pow2(temp_s2.len()) + Str2Int(temp_s1@) * Str2Int(temp_s2@) == Str2Int(s1@) * Str2Int(s2@),
        decreases temp_s2.len()
    {
        let last_char = temp_s2.pop().unwrap();
        
        if last_char == '1' {
            let mut new_result = Vec::<char>::new();
            new_result.extend(result.iter().chain(temp_s1.iter()));
            result = new_result;
        } else {
            proof {
                helper_lemma_str2int_append_zero(result@);
            }
        }
        
        let mut new_temp_s1 = Vec::<char>::new();
        new_temp_s1.push('0');
        new_temp_s1.extend(temp_s1.iter());
        temp_s1 = new_temp_s1;
    }
    
    result
}
// </vc-code>

fn main() {}
}
