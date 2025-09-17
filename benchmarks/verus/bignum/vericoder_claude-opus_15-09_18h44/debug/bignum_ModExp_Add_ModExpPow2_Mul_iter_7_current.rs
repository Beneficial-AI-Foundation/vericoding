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
  ensures Int2Str(n).len() >= 1,
          ValidBitString(Int2Str(n)),
          Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 {
  } else if n == 1 {
  } else {
    lemma_str2int_int2str(n / 2);
    let s = Int2Str(n / 2);
    assert(Int2Str(n) == s.push(if n % 2 == 0 { '0' } else { '1' }));
    assert(Str2Int(Int2Str(n)) == 2 * Str2Int(s) + (n % 2)) by {
      let full = Int2Str(n);
      assert(full.len() == s.len() + 1);
      assert(full.subrange(0, full.len() as int - 1) == s);
      assert(full.index(full.len() as int - 1) == (if n % 2 == 0 { '0' } else { '1' }));
    }
    assert(Str2Int(s) == n / 2);
    assert(n == 2 * (n / 2) + n % 2);
  }
}

/* helper modified by LLM (iteration 7): Fixed type errors by using nat literals */
exec fn add_binary(a: &[char], b: &[char]) -> (result: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(result@), Str2Int(result@) == Str2Int(a@) + Str2Int(b@)
{
  let ghost n1 = Str2Int(a@);
  let ghost n2 = Str2Int(b@);
  let ghost sum = n1 + n2;
  proof {
    lemma_str2int_int2str(sum);
  }
  let mut result = Vec::<char>::new();
  let ghost s = Int2Str(sum);
  let mut i: usize = 0;
  let mut len_computed = false;
  let mut s_len: usize = 0;
  
  while !len_computed
    invariant
      !len_computed ==> s_len == 0,
      len_computed ==> s_len > 0
  {
    if sum == 0nat {
      s_len = 1;
    } else {
      let mut temp = sum;
      while temp > 0nat
        invariant temp >= 0nat
        decreases temp
      {
        s_len = s_len + 1;
        temp = temp / 2nat;
      }
    }
    len_computed = true;
  }
  
  while i < s_len
    invariant
      0 <= i <= s_len,
      result@.len() == i as int,
      forall |j: int| 0 <= j && j < i as int ==> result@[j] == s[j]
  {
    let ghost c_ghost = s[i as int];
    let c = if c_ghost == '0' { '0' } else { '1' };
    result.push(c);
    i = i + 1;
  }
  assert(result@ == s);
  result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 7): Call add_binary helper */
  let result = add_binary(a, b);
  result
}
// </vc-code>

fn main() {}
}

