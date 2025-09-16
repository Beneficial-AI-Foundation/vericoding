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
use vstd::arithmetic::power2::pow2;

proof fn lemma_str2int_bounds(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s) < pow2(s.len() as nat)
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
        assert(pow2(0nat) == 1);
    } else {
        lemma_str2int_bounds(s.subrange(0, s.len() as int - 1));
        let prefix = s.subrange(0, s.len() as int - 1);
        assert(Str2Int(prefix) < pow2((s.len() - 1) as nat));
        let last_bit = if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat };
        assert(Str2Int(s) == 2 * Str2Int(prefix) + last_bit);
        assert(Str2Int(s) < 2 * pow2((s.len() - 1) as nat));
        assert(2 * pow2((s.len() - 1) as nat) == pow2(s.len() as nat)) by {
            vstd::arithmetic::power2::lemma_pow2_unfold(s.len() as nat);
        }
    }
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s.push('0')) == 2 * Str2Int(s)
{
    assert(s.push('0').subrange(0, s.push('0').len() as int - 1) == s);
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
    assert(s.push('1').subrange(0, s.push('1').len() as int - 1) == s);
}

/* helper modified by LLM (iteration 10): fixed type annotation for decreases clause */
exec fn subtract_with_borrow(a: char, b: char, borrow: bool) -> (res: (char, bool))
    requires
        a == '0' || a == '1',
        b == '0' || b == '1'
    ensures
        res.0 == '0' || res.0 == '1',
        (if a == '1' { 1int } else { 0int }) + (if res.1 { 2int } else { 0int }) == (if b == '1' { 1int } else { 0int }) + (if borrow { 1int } else { 0int }) + (if res.0 == '1' { 1int } else { 0int })
{
    let a_val = if a == '1' { 1 } else { 0 };
    let b_val = if b == '1' { 1 } else { 0 };
    let borrow_val = if borrow { 1 } else { 0 };
    
    if a_val >= b_val + borrow_val {
        let res_val = a_val - b_val - borrow_val;
        (if res_val == 1 { '1' } else { '0' }, false)
    } else {
        let res_val = 2 + a_val - b_val - borrow_val;
        (if res_val == 1 { '1' } else { '0' }, true)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Sub(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@), Str2Int(s1@) >= Str2Int(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) - Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fixed type annotation in decreases clause */
    let mut result = Vec::<char>::new();
    let mut borrow = false;
    let mut i: usize = 0;
    
    let s1_len = s1.len();
    let s2_len = s2.len();
    
    while i < s1_len || i < s2_len || borrow
        invariant
            i <= s1_len,
            i <= s2_len,
            ValidBitString(result@),
            result@.len() == i,
            forall |k: int| 0 <= k && k < i as int ==> (result@[k] == '0' || result@[k] == '1'),
        decreases (if i < s1_len { s1_len - i } else { 0 }) + (if i < s2_len { s2_len - i } else { 0 }) + (if borrow { 1int } else { 0int })
    {
        let a = if i < s1_len { s1[s1_len - 1 - i] } else { '0' };
        let b = if i < s2_len { s2[s2_len - 1 - i] } else { '0' };
        
        assert(i < s1_len ==> s1_len - 1 - i < s1_len && s1_len - 1 - i >= 0);
        assert(i < s2_len ==> s2_len - 1 - i < s2_len && s2_len - 1 - i >= 0);
        
        let (digit, new_borrow) = subtract_with_borrow(a, b, borrow);
        result.push(digit);
        borrow = new_borrow;
        i = i + 1;
    }
    
    // Remove leading zeros (from the end since we're building in reverse)
    while result.len() > 1 && result[result.len() - 1] == '0'
        invariant
            result.len() >= 1,
            ValidBitString(result@),
        decreases result.len()
    {
        result.pop();
    }
    
    // Reverse the result
    let mut reversed = Vec::<char>::new();
    let mut j: usize = 0;
    while j < result.len()
        invariant
            j <= result.len(),
            reversed@.len() == j,
            forall |k: int| 0 <= k && k < j as int ==> (reversed@[k] == '0' || reversed@[k] == '1'),
            forall |k: int| 0 <= k && k < j as int ==> reversed@[k] == result@[result.len() as int - 1 - k],
        decreases result.len() - j
    {
        reversed.push(result[result.len() - 1 - j]);
        j = j + 1;
    }
    
    assert(ValidBitString(reversed@));
    
    reversed
}
// </vc-code>

fn main() {}
}


