// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t),
    t.len() > 0,
    t.len() > 1 ==> t[0] != '0',
    valid_bit_string(s) ==> str2int(s) == str2int(t)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): introduce int2bits and its correctness lemmas; strengthen push lemma */
spec fn int2bits(n: nat) -> Seq<char>
  decreases n
{
    if n == 0nat {
        Seq::<char>::empty()
    } else {
        int2bits(n / 2).push(if n % 2 == 1nat { '1' } else { '0' })
    }
}

/* helper modified by LLM (iteration 10): validity is preserved when pushing a bit */
proof fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
  requires valid_bit_string(s), c == '0' || c == '1'
  ensures valid_bit_string(s.push(c))
{
    assert(s.push(c).len() == s.len() + 1);
    assert(forall|i: int| 0 <= i < s.push(c).len() ==> (
        if i < s.len() { s[i] == '0' || s[i] == '1' } else { c == '0' || c == '1' }
    ));
}

/* helper modified by LLM (iteration 10): lemma about str2int structure when pushing a bit */
proof fn lemma_str2int_push(s: Seq<char>, c: char)
  requires valid_bit_string(s), c == '0' || c == '1'
  ensures str2int(s.push(c)) == 2nat * str2int(s) + (if c == '1' { 1nat } else { 0nat })
{
    let t = s.push(c);
    proof { lemma_valid_bit_string_push(s, c); }
    assert(t.len() == s.len() + 1);
    assert(t.subrange(0, t.len() - 1) == s);
    assert(t[t.len() - 1] == c);
    assert(
        str2int(t)
        == 2nat * str2int(t.subrange(0, t.len() - 1))
           + (if t[t.len() - 1] == '1' { 1nat } else { 0nat })
    );
    assert(str2int(s.push(c)) == 2nat * str2int(s) + (if c == '1' { 1nat } else { 0nat }));
}

/* helper modified by LLM (iteration 10): int2bits produces valid bit strings */
proof fn lemma_int2bits_valid(n: nat)
  ensures valid_bit_string(int2bits(n))
{
    if n == 0nat {
        // empty sequence is vacuously a valid bit string
    } else {
        lemma_int2bits_valid(n / 2);
        let c = if n % 2 == 1nat { '1' } else { '0' };
        lemma_valid_bit_string_push(int2bits(n / 2), c);
        assert(valid_bit_string(int2bits(n / 2).push(c)));
    }
}

/* helper modified by LLM (iteration 10): correctness of int2bits w.r.t. str2int */
proof fn lemma_int2bits_value(n: nat)
  ensures str2int(int2bits(n)) == n
{
    if n == 0nat {
        assert(str2int(int2bits(0nat)) == 0nat);
    } else {
        lemma_int2bits_valid(n / 2);
        lemma_int2bits_value(n / 2);
        let c = if n % 2 == 1nat { '1' } else { '0' };
        lemma_str2int_push(int2bits(n / 2), c);
        assert((if c == '1' { 1nat } else { 0nat }) == (if n % 2 == 1nat { 1nat } else { 0nat }));
        assert(str2int(int2bits(n)) == 2nat * str2int(int2bits(n / 2)) + (if n % 2 == 1nat { 1nat } else { 0nat }));
        assert(str2int(int2bits(n / 2)) == n / 2);
        assert(0nat <= n % 2 && n % 2 < 2nat);
        assert(2nat * (n / 2) + (if n % 2 == 1nat { 1nat } else { 0nat }) == n);
        assert(str2int(int2bits(n)) == n);
    }
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) * str2int(s2@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 10): use Vec::from(seq) instead of non-existent from_seq; prove ensures via helpers */
  let t = int2bits(str2int(s1@) * str2int(s2@));
  let res: Vec<char> = Vec::from(t);
  proof {
      lemma_int2bits_valid(str2int(s1@) * str2int(s2@));
      lemma_int2bits_value(str2int(s1@) * str2int(s2@));
      assert(res@ == t);
      assert(valid_bit_string(res@));
      assert(str2int(res@) == str2int(s1@) * str2int(s2@));
  }
  res
}
// </vc-code>


}

fn main() {}