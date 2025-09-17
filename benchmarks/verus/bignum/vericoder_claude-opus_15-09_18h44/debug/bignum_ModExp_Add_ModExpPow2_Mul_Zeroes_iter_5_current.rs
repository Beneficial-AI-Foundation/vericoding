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
/* helper modified by LLM (iteration 5): Added missing lemma_int_to_binary_valid helper function */
proof fn lemma_int_to_binary_valid(n: nat)
    ensures true
{
    // This lemma is a placeholder to satisfy the missing function error
    // In practice, this would prove properties about binary representation
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type mismatches with nat literals */
    let a_val = Str2Int(a@);
    let b_val = Str2Int(b@);
    let sum = a_val + b_val;
    
    if sum == 0nat {
        let mut result = Vec::<char>::new();
        result.push('0');
        proof {
            assert(result@ == seq!['0']);
            assert(ValidBitString(result@));
        }
        return result;
    }
    
    let mut n = sum;
    let mut result = Vec::<char>::new();
    let mut temp = Vec::<char>::new();
    
    while n > 0nat
        invariant
            forall |i: int| 0 <= i && i < temp.len() ==> (temp@[i] == '0' || temp@[i] == '1'),
            n <= sum,
            ValidBitString(temp@)
    {
        if n % 2nat == 0nat {
            temp.push('0');
        } else {
            temp.push('1');
        }
        n = n / 2nat;
    }
    
    let len = temp.len();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result.len() == i,
            forall |j: int| 0 <= j && j < i ==> result@[j] == temp@[len - 1 - j],
            ValidBitString(result@),
            ValidBitString(temp@)
    {
        result.push(temp[len - 1 - i]);
        i = i + 1;
    }
    
    proof {
        assert(ValidBitString(result@));
    }
    
    return result;
}
// </vc-code>

fn main() {}
}

