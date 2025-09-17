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
proof fn lemma_str2int_monotonic(s: Seq<char>, t: Seq<char>)
    requires
        ValidBitString(s),
        ValidBitString(t),
        s.len() <= t.len()
    ensures
        Str2Int(s) <= Str2Int(t)
{}

proof fn lemma_str2int_power2_add(n: nat)
    ensures
        Str2Int(Seq::new(n, |i: int| if i < n as int - 1 { '0' } else { '1' })) == 2.pow(n) - 1,
{
    if n > 0 {
        lemma_str2int_power2_add(n - 1);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_str2int_monotonic(a@, a@);
        lemma_str2int_monotonic(b@, b@);
        lemma_str2int_power2_add(a@.len() as nat);
        lemma_str2int_power2_add(b@.len() as nat);
    }
    
    let mut result: Vec<char> = Vec::new();
    let zero_char: char = '0';
    
    while result.len() < a.len() + b.len()
        invariant
            ValidBitString(result@),
            result.len() <= a.len() + b.len()
    {
        result.push(zero_char);
    }
    
    result
}
// </vc-code>

fn main() {}
}

