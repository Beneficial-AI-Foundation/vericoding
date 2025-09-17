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
proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
    let s_new = s.push('0');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) =~= s);
    assert(s_new.index(s_new.len() as int - 1) == '0');
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
    let s_new = s.push('1');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) =~= s);
    assert(s_new.index(s_new.len() as int - 1) == '1');
}

/* helper modified by LLM (iteration 5): Fixed trigger issue in invariant */
exec fn add_binary(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(a@),
        ValidBitString(b@),
    ensures
        ValidBitString(res@),
        Str2Int(res@) == (Str2Int(a@) + Str2Int(b@)) % vstd::arithmetic::power2::pow2((if a@.len() > b@.len() { a@.len() } else { b@.len() }) + 1)
{
    let mut result = Vec::<char>::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    while i < max_len
        invariant
            i <= max_len,
            carry <= 1,
            result.len() == i,
            ValidBitString(result@),
        decreases max_len - i
    {
        let a_bit = if i < a.len() && a[a.len() - 1 - i] == '1' { 1u8 } else { 0u8 };
        let b_bit = if i < b.len() && b[b.len() - 1 - i] == '1' { 1u8 } else { 0u8 };
        let sum = a_bit + b_bit + carry;
        
        if sum % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        carry = sum / 2;
        i = i + 1;
    }
    
    if carry == 1 {
        result.push('1');
    }
    
    let mut final_result = Vec::<char>::new();
    let mut j: usize = result.len();
    while j > 0
        invariant
            j <= result.len(),
            final_result.len() == result.len() - j,
            ValidBitString(result@),
            forall |k: int| #[trigger] final_result@[k] ==>
                0 <= k && k < final_result.len() as int ==> {
                    let idx = result.len() - 1 - k;
                    idx < result.len() && final_result@[k] == result@[idx] && (result@[idx] == '0' || result@[idx] == '1')
                },
        decreases j
    {
        j = j - 1;
        final_result.push(result[j]);
    }
    
    if final_result.len() == 0 {
        final_result.push('0');
    }
    
    final_result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Call the fixed add_binary helper function */
    let result = add_binary(a, b);
    result
}
// </vc-code>

fn main() {}
}

