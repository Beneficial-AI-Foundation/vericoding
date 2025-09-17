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
proof fn lemma_concat_valid_bit_strings(a: Seq<char>, b: Seq<char>)
  requires ValidBitString(a), ValidBitString(b)
  ensures ValidBitString(a + b)
{
  assert forall |i: int| 0 <= i < (a + b).len() implies 
    #[trigger] (a + b)[i] == '0' || (a + b)[i] == '1' by {
    let combined = a + b;
    if i < a.len() {
      assert(combined[i] == a[i]);
      assert(a[i] == '0' || a[i] == '1');
    } else {
      assert(combined[i] == b[i - a.len()]);
      assert(b[i - a.len()] == '0' || b[i - a.len()] == '1');
    }
  };
}

proof fn lemma_push_preserves_valid_bit_string(v: Seq<char>, c: char)
  requires ValidBitString(v), c == '0' || c == '1'
  ensures ValidBitString(v.push(c))
{
  assert forall |i: int| 0 <= i < v.push(c).len() implies 
    #[trigger] v.push(c)[i] == '0' || v.push(c)[i] == '1' by {
    if i < v.len() {
      assert(v.push(c)[i] == v[i]);
      assert(v[i] == '0' || v[i] == '1');
    } else {
      assert(i == v.len());
      assert(v.push(c)[i] == c);
      assert(c == '0' || c == '1');
    }
  };
}

proof fn lemma_slice_preserves_valid_bit_string(a: &[char])
  requires ValidBitString(a@)
  ensures forall |i: int| 0 <= i < (a@).len() ==> ((a@)[i] == '0' || (a@)[i] == '1')
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
  let mut res = Vec::<char>::new();
  
  for i in 0..a.len()
    invariant ValidBitString(res@)
  {
    proof {
      lemma_slice_preserves_valid_bit_string(a);
      assert(0 <= i as int < (a@).len());
      assert((a@)[i as int] == '0' || (a@)[i as int] == '1');
      lemma_push_preserves_valid_bit_string(res@, (a@)[i as int]);
    }
    res.push(a[i]);
  }
  
  for i in 0..b.len()
    invariant ValidBitString(res@)
  {
    proof {
      lemma_slice_preserves_valid_bit_string(b);
      assert(0 <= i as int < (b@).len());
      assert((b@)[i as int] == '0' || (b@)[i as int] == '1');
      lemma_push_preserves_valid_bit_string(res@, (b@)[i as int]);
    }
    res.push(b[i]);
  }
  
  res
}
// </vc-code>

fn main() {}
}