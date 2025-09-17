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
proof fn lemma_str2int_bounds(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < pow2(s.len() as nat)
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_bounds(s.subrange(0, s.len() as int - 1));
    }
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

spec fn add_binary(a: Seq<char>, b: Seq<char>) -> Seq<char>
    recommends ValidBitString(a),
        ValidBitString(b)
{
    int_to_binary((Str2Int(a) + Str2Int(b)) as nat)
}

spec fn int_to_binary(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1']
    } else {
        int_to_binary(n / 2).push(if n % 2 == 0 { '0' } else { '1' })
    }
}

proof fn lemma_int_to_binary_valid(n: nat)
    ensures ValidBitString(int_to_binary(n))
    decreases n
{
    if n <= 1 {
    } else {
        lemma_int_to_binary_valid(n / 2);
    }
}

/* helper modified by LLM (iteration 2): added decreases clause to loops */
exec fn add_binary_strings(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@),
        ValidBitString(b@)
    ensures ValidBitString(res@),
        Str2Int(res@) == (Str2Int(a@) + Str2Int(b@)) % pow2(res@.len() as nat)
{
    let mut carry = 0u8;
    let mut result = Vec::new();
    let mut i = 0;
    let a_len = a.len();
    let b_len = b.len();
    
    while i < a_len || i < b_len || carry != 0
        invariant
            i <= a_len,
            i <= b_len,
            carry <= 1,
            ValidBitString(result@),
            result@.len() == i,
        decreases (if a_len >= b_len { a_len } else { b_len }) - i + carry
    {
        let mut sum = carry;
        if i < a_len {
            if a[a_len - 1 - i] == '1' {
                sum = sum + 1;
            }
        }
        if i < b_len {
            if b[b_len - 1 - i] == '1' {
                sum = sum + 1;
            }
        }
        
        if sum % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        carry = sum / 2;
        i = i + 1;
    }
    
    let mut j = 0;
    let mut reversed = Vec::new();
    while j < result.len()
        invariant
            j <= result.len(),
            ValidBitString(reversed@),
            reversed@.len() == j,
        decreases result.len() - j
    {
        reversed.push(result[result.len() - 1 - j]);
        j = j + 1;
    }
    
    reversed
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): using helper function */
    proof {
        lemma_int_to_binary_valid((Str2Int(a@) + Str2Int(b@)) as nat);
    }
    add_binary_strings(a, b)
}
// </vc-code>

fn main() {}
}

