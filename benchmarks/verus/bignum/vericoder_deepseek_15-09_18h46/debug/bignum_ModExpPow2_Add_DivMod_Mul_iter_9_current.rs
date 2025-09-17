
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
/* helper modified by LLM (iteration 9): Fixed pow2_add1 lemma usage with proper syntax */
proof fn pow2_add1(i: nat)
    ensures pow2(i + 1) == 2 * pow2(i)
{
    vstd::arithmetic::power2::pow2_add1(i);
}

proof fn lemma_str2int_nonnegative(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
    } else {
        lemma_str2int_nonnegative(s.subrange(0, s.len() as int - 1));
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + 
            (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
    }
}

proof fn lemma_str2int_monotonic(s: Seq<char>, t: Seq<char>)
    requires ValidBitString(s), ValidBitString(t), s.len() <= t.len()
    ensures Str2Int(s) <= Str2Int(t)
    decreases s.len()
{
    if s.len() == 0 {
        lemma_str2int_nonnegative(t);
        assert(Str2Int(s) == 0);
    } else {
        lemma_str2int_monotonic(s.subrange(0, s.len() as int - 1), t.subrange(0, t.len() as int - 1));
        let s_last = s.index(s.len() as int - 1);
        let t_last = t.index(t.len() as int - 1);
        let s_val = if s_last == '1' { 1nat } else { 0nat };
        let t_val = if t_last == '1' { 1nat } else { 0nat };
        assert(s_val <= t_val);
    }
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(Seq::empty().push('0')) == 0);
        assert(2 * Str2Int(Seq::empty()) == 0);
    } else {
        lemma_str2int_append_zero(s.subrange(0, s.len() as int - 1));
        let last_char = s.index(s.len() as int - 1);
        let last_val = if last_char == '1' { 1nat } else { 0nat };
        assert(Str2Int(s.push('0')) == 2 * Str2Int(s.subrange(0, s.len() as int - 1).push('0')) + last_val);
        assert(2 * Str2Int(s) == 2 * (2 * Str2Int(s.subrange(0, s.len() as int - 1)) + last_val));
        assert(2 * Str2Int(s.subrange(0, s.len() as int - 1).push('0')) == 4 * Str2Int(s.subrange(0, s.len() as int - 1)));
    }
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(Seq::empty().push('1')) == 1);
        assert(2 * Str2Int(Seq::empty()) + 1 == 1);
    } else {
        lemma_str2int_append_one(s.subrange(0, s.len() as int - 1));
        let last_char = s.index(s.len() as int - 1);
        let last_val = if last_char == '1' { 1nat } else { 0nat };
        assert(Str2Int(s.push('1')) == 2 * Str2Int(s.subrange(0, s.len() as int - 1).push('1')) + last_val);
        assert(2 * Str2Int(s) + 1 == 2 * (2 * Str2Int(s.subrange(0, s.len() as int - 1)) + last_val) + 1);
        assert(2 * Str2Int(s.subrange(0, s.len() as int - 1).push('1')) == 4 * Str2Int(s.subrange(0, s.len() as int - 1)) + 2);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Fixed pow2_add1 call with proper lemma usage */
{
    let mut result = Vec::new();
    let mut carry = 0;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    let mut i = 0;
    while i < max_len || carry > 0
        invariant
            0 <= i,
            carry >= 0 && carry <= 2,
            ValidBitString(result@),
            result.len() == i,
            Str2Int(result@) + carry * (pow2(i as nat)) == Str2Int(a@) + Str2Int(b@)
        decreases (max_len as int - i) + carry as int
    {
        let a_bit = if i < a.len() && a[i] == '1' { 1 } else { 0 };
        let b_bit = if i < b.len() && b[i] == '1' { 1 } else { 0 };
        let sum = a_bit + b_bit + carry;
        
        if sum % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        
        carry = sum / 2;
        
        proof {
            lemma_str2int_nonnegative(result@);
            lemma_str2int_nonnegative(a@);
            lemma_str2int_nonnegative(b@);
            pow2_add1(i as nat);
            assert(pow2((i + 1) as nat) == 2 * pow2(i as nat));
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}

