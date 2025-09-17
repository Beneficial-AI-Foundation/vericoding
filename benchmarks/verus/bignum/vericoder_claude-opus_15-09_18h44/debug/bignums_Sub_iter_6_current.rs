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
    } else {
        lemma_str2int_bounds(s.subrange(0, s.len() as int - 1));
        assert(Str2Int(s.subrange(0, s.len() as int - 1)) < pow2((s.len() - 1) as nat));
        assert(pow2((s.len() - 1) as nat) * 2 == pow2(s.len() as nat));
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

/* helper modified by LLM (iteration 6): fixed ensures clause syntax */
exec fn subtract_with_borrow(a: char, b: char, borrow: bool) -> (res: (char, bool))
    requires
        a == '0' || a == '1',
        b == '1' || b == '0'
    ensures
        res.0 == '0' || res.0 == '1',
        (if a == '1' { 1int } else { 0int }) >= (if b == '1' { 1int } else { 0int }) + (if borrow { 1int } else { 0int }) + (if res.1 { 2int } else { 0int }) - (if res.0 == '1' { 1int } else { 0int })
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
    /* code modified by LLM (iteration 6): added decreases clause to while loops */
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
            if i == 0 && !borrow {
                Str2Int(result@) == 0
            } else {
                let s1_prefix = s1@.subrange(s1_len as int - i as int, s1_len as int);
                let s2_prefix = if i <= s2_len { s2@.subrange(s2_len as int - i as int, s2_len as int) } else { seq![] };
                Str2Int(s1_prefix) >= Str2Int(s2_prefix) + (if borrow { 1nat } else { 0nat }) &&
                Str2Int(result@) == Str2Int(s1_prefix) - Str2Int(s2_prefix) - (if borrow { 1nat } else { 0nat })
            },
        decreases (s1_len - i) + (s2_len - i) + (if borrow { 1 } else { 0 })
    {
        let a = if i < s1_len { s1[s1_len - 1 - i] } else { '0' };
        let b = if i < s2_len { s2[s2_len - 1 - i] } else { '0' };
        
        let (digit, new_borrow) = subtract_with_borrow(a, b, borrow);
        result.push(digit);
        borrow = new_borrow;
        i = i + 1;
    }
    
    // Remove leading zeros
    while result.len() > 0 && result[result.len() - 1] == '0'
        invariant
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@) - Str2Int(s2@),
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
            ValidBitString(reversed@),
            reversed@.len() == j,
            forall |k: int| 0 <= k && k < j as int ==> reversed@[k] == result@[result.len() as int - 1 - k],
        decreases result.len() - j
    {
        reversed.push(result[result.len() - 1 - j]);
        j = j + 1;
    }
    
    reversed
}
// </vc-code>

fn main() {}
}


