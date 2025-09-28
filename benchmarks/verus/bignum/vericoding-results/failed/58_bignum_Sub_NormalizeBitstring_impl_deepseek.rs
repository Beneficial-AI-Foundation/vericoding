// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t) &&
    t.len() > 0 &&
    (t.len() > 1 ==> t[0] != '0') &&
    (valid_bit_string(s) ==> str2int(s) == str2int(t))
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fix type annotations and subrange parameter types */
proof fn lemma_str2int_nonnegative(s: Seq<char>) 
  requires valid_bit_string(s)
  ensures str2int(s) >= 0
  decreases s.len()
{
  if s.len() > 0 {
    lemma_str2int_nonnegative(s.subrange(0, s.len() - 1));
  }
}

proof fn lemma_str2int_concat(s: Seq<char>, c: char)
  requires valid_bit_string(s) && (c == '0' || c == '1')
  ensures str2int(s.push(c)) == 2 * str2int(s) + (if c == '1' {1int} else {0int})
  decreases s.len()
{
  if s.len() == 0 {
    assert(str2int(Seq::empty().push(c)) == (if c == '1' {1nat} else {0nat}));
    assert(2 * str2int(Seq::empty()) + (if c == '1' {1int} else {0int}) == (if c == '1' {1int} else {0int}));
  } else {
    let last = s[s.len() - 1];
    let prefix = s.subrange(0, s.len() - 1);
    lemma_str2int_concat(prefix, last);
    assert(str2int(s) == 2 * str2int(prefix) + (if last == '1' {1nat} else {0nat}));
    assert(str2int(s.push(c)) == 2 * str2int(s) + (if c == '1' {1nat} else {0nat}));
  }
}

spec fn find_first_nonzero(s: Seq<char>) -> (result: int)
  requires valid_bit_string(s) && s.len() > 0 && str2int(s) > 0
  ensures 
    0 <= result < s.len(),
    s[result] == '1',
    forall|i: int| 0 <= i < result ==> s[i] == '0'
{
  choose|i: int| 0 <= i < s.len() && s[i] == '1'
}

fn remove_leading_zeros(s: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s@) && s.len() > 0
  ensures 
    valid_bit_string(res@) && res.len() > 0,
    (res[0] == '0' ==> res.len() == 1),
    (res[0] == '1' ==> forall|i: int| 0 <= i < res.len() ==> res@[i] == res@[i]),
    str2int(res@) == str2int(s@)
{
  if s[0] == '1' {
    s
  } else {
    let mut i = 0;
    
    while i < s.len() && s[i] == '0'
      invariant 
        0 <= i <= s.len(),
        forall|j: int| 0 <= j < i ==> s@[j] == '0',
        str2int(s@) == str2int(s@.subrange(i as int, s.len() as int)) * 2.pow(i as nat)
    {
      proof {
        lemma_str2int_nonnegative(s@.subrange(i as int, s.len() as int));
        assert(str2int(s@) == str2int(s@.subrange(i as int, s.len() as int)) * 2.pow(i as nat));
        assert(s@.subrange(i as int, s.len() as int).len() == s.len() - i);
      }
      if i < s.len() - 1 {
        proof {
          assert(s@.subrange(i as int, s.len() as int).push(s[i]) == s@.subrange((i - 1) as int, s.len() as int));
        }
        i = i + 1;
      } else {
        break;
      }
    }
    
    let res_vec = s[i..].to_vec();
    
    if res_vec.len() == 0 {
      let mut single_zero = Vec::new();
      single_zero.push('0');
      single_zero
    } else {
      res_vec
    }
  }
}
// </vc-helpers>

// <vc-spec>
fn sub(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@) &&
    str2int(s1@) >= str2int(s2@)
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) - str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fix type annotations and use proper slicing */
    let mut s1_vec = s1.clone();
    let mut s2_vec = s2.clone();
    
    let len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    let mut result = Vec::with_capacity(len);
    let mut borrow = 0;
    
    for i in 0..len {
        let idx1 = s1.len() - 1 - i;
        let idx2 = s2.len() - 1 - i;
        
        let bit1 = if idx1 < s1.len() { if s1_vec[idx1] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if idx2 < s2.len() { if s2_vec[idx2] == '1' { 1 } else { 0 } } else { 0 };
        
        let mut diff = bit1 - bit2 - borrow;
        borrow = 0;
        
        if diff < 0 {
            diff += 2;
            borrow = 1;
        }
        
        result.insert(0, if diff == 1 { '1' } else { '0' });
    }
    
    while result.len() > 1 && result[0] == '0' {
        result.remove(0);
    }
    
    if result.is_empty() {
        let mut zero = Vec::new();
        zero.push('0');
        zero
    } else {
        result
    }
}
// </vc-code>


}

fn main() {}