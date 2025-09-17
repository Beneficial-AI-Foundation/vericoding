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
/* helper modified by LLM (iteration 5): Adding reverse function spec to avoid compilation error */
spec fn reverse_spec(s: Seq<char>) -> Seq<char> {
  if s.len() == 0 {
    seq![]
  } else {
    reverse_spec(s.subrange(1, s.len() as int)) + seq![s[0]]
  }
}

proof fn lemma_reverse_preserves_validity(s: Seq<char>)
  requires ValidBitString(s)
  ensures ValidBitString(reverse_spec(s))
{
  if s.len() > 0 {
    lemma_reverse_preserves_validity(s.subrange(1, s.len() as int));
  }
}

/* helper modified by LLM (iteration 5): Adding helper for binary addition correctness */
proof fn lemma_addition_algorithm(a: Seq<char>, b: Seq<char>)
  requires
    ValidBitString(a),
    ValidBitString(b)
  ensures
    ValidBitString(reverse_spec(// Implementation goes here to connect algorithm to spec
  )
{
  // Proof logic for binary addition
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implementing custom reverse to avoid unsupported std function */
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
    
    // Manual reverse implementation to avoid unsupported std function
    let mut reversed = Vec::with_capacity(res.len());
    let mut idx = res.len() as isize - 1;
    while idx >= 0 {
        reversed.push(res[idx as usize]);
        idx -= 1;
    }
    
    reversed
}
// </vc-code>

fn main() {}
}

