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
/* helper modified by LLM (iteration 7): Fixed Str2Int base cases and lemma logic */
spec fn Int2Str(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    seq!['0']
  } else if n == 1 {
    seq!['1']
  } else {
    Int2Str(n / 2).push(if n % 2 == 0 { '0' } else { '1' })
  }
}

proof fn lemma_str2int_int2str(n: nat)
  ensures ValidBitString(Int2Str(n)),
          Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 {
    let s = seq!['0'];
    assert(Int2Str(0) == s);
    assert(s.len() == 1);
    assert(s[0] == '0');
    assert(ValidBitString(s)) by {
      assert(forall |i: int| 0 <= i && i < s.len() ==> s[i] == '0' || s[i] == '1');
    }
    assert(Str2Int(s) == 0) by {
      assert(s.len() == 1);
      assert(s.subrange(0, 0).len() == 0);
      assert(Str2Int(s.subrange(0, 0)) == 0);
      assert(s[0] == '0');
      assert(Str2Int(s) == 2 * 0 + 0);
    }
  } else if n == 1 {
    let s = seq!['1'];
    assert(Int2Str(1) == s);
    assert(s.len() == 1);
    assert(s[0] == '1');
    assert(ValidBitString(s)) by {
      assert(forall |i: int| 0 <= i && i < s.len() ==> s[i] == '0' || s[i] == '1');
    }
    assert(Str2Int(s) == 1) by {
      assert(s.len() == 1);
      assert(s.subrange(0, 0).len() == 0);
      assert(Str2Int(s.subrange(0, 0)) == 0);
      assert(s[0] == '1');
      assert(Str2Int(s) == 2 * 0 + 1);
    }
  } else {
    lemma_str2int_int2str(n / 2);
    let s = Int2Str(n / 2);
    let c = if n % 2 == 0 { '0' } else { '1' };
    assert(Int2Str(n) == s.push(c));
    assert(ValidBitString(s));
    assert(c == '0' || c == '1');
    assert(ValidBitString(Int2Str(n))) by {
      assert(forall |i: int| 0 <= i && i < s.len() ==> Int2Str(n)[i] == s[i]);
      assert(Int2Str(n)[s.len() as int] == c);
    }
    assert(Str2Int(Int2Str(n)) == n) by {
      let full = Int2Str(n);
      assert(full == s.push(c));
      assert(full.len() == s.len() + 1);
      assert(full.subrange(0, full.len() - 1) == s);
      assert(full[full.len() - 1] == c);
      assert(Str2Int(full) == 2 * Str2Int(s) + if c == '1' { 1nat } else { 0nat });
      assert(Str2Int(s) == n / 2);
      assert(if c == '1' { 1nat } else { 0nat } == n % 2);
    }
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): Fixed type error by using j as int for indexing */
{
  let mut result = Vec::<char>::new();
  
  let max_len = if a.len() > b.len() { a.len() } else { b.len() };
  let mut carry: u8 = 0;
  let mut i: usize = 0;
  
  while i < max_len || carry > 0
    invariant
      ValidBitString(result@),
      carry <= 1,
      i <= max_len + if carry > 0 { 1 } else { 0 },
      result@.len() == i
    decreases if i < max_len { max_len - i + 1 } else if carry > 0 { 1 } else { 0 }
  {
    let mut sum = carry;
    
    if i < a.len() {
      let a_idx = a.len() - 1 - i;
      if a[a_idx] == '1' {
        sum = sum + 1;
      }
    }
    
    if i < b.len() {
      let b_idx = b.len() - 1 - i;
      if b[b_idx] == '1' {
        sum = sum + 1;
      }
    }
    
    if sum % 2 == 1 {
      result.push('1');
    } else {
      result.push('0');
    }
    assert(result@[result@.len() - 1] == '0' || result@[result@.len() - 1] == '1');
    
    carry = sum / 2;
    i = i + 1;
    assert(carry <= 1);
  }
  
  // Reverse the result
  let mut reversed = Vec::<char>::new();
  let mut j: usize = result.len();
  while j > 0
    invariant
      ValidBitString(result@),
      ValidBitString(reversed@),
      j <= result.len(),
      reversed@.len() == result.len() - j,
      forall |k: int| 0 <= k && k < reversed@.len() ==> reversed@[k] == result@[result@.len() - 1 - k]
    decreases j
  {
    j = j - 1;
    let c = result[j];
    reversed.push(c);
    assert(c == result@[j as int]);
    assert(ValidBitString(result@));
    assert(c == '0' || c == '1');
  }
  
  reversed
}
// </vc-code>

fn main() {}
}

