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
/* helper modified by LLM (iteration 10): add nat2bits and supporting lemmas for correctness and validity */
spec fn nat2bits(n: nat) -> Seq<char>
  decreases n
{
  if n == 0nat {
    seq!['0']
  } else {
    let b: char = if n % 2nat == 1nat { '1' } else { '0' };
    nat2bits(n / 2nat) + seq![b]
  }
}

/* helper modified by LLM (iteration 10): prove unfolding of str2int on append */
proof fn lemma_str2int_concat_char(s: Seq<char>, c: char)
  ensures
    str2int(s + seq![c]) == 2nat * str2int(s) + (if c == '1' { 1nat } else { 0nat })
{
  let sc = s + seq![c];
  assert(sc.len() == s.len() + 1);
  assert(sc.len() > 0);
  assert(sc.subrange(0, sc.len() - 1) == s);
  assert(sc[sc.len() - 1] == c);
  assert(str2int(sc) == 2nat * str2int(sc.subrange(0, sc.len() - 1)) + (if sc[sc.len() - 1] == '1' { 1nat } else { 0nat }));
  assert(str2int(s + seq![c]) == 2nat * str2int(s) + (if c == '1' { 1nat } else { 0nat }));
}

/* helper modified by LLM (iteration 10): appending a bit preserves validity */
proof fn lemma_valid_concat(s: Seq<char>, c: char)
  requires
    valid_bit_string(s),
    c == '0' || c == '1'
  ensures
    valid_bit_string(s + seq![c])
{
  assert forall|i: int|
    0 <= i < (s + seq![c]).len()
    implies (s + seq![c])[i] == '0' || (s + seq![c])[i] == '1' by
  {
    if i < s.len() {
      assert((s + seq![c])[i] == s[i]);
    } else {
      assert(i == s.len());
      assert((s + seq![c])[i] == c);
    }
  }
}

/* helper modified by LLM (iteration 10): lemma for mod-2 decomposition */
proof fn lemma_mod2_decomp(n: nat)
  ensures
    2nat * (n / 2nat) + (if n % 2nat == 1nat { 1nat } else { 0nat }) == n
{
  assert(n == 2nat * (n / 2nat) + n % 2nat);
  let r = n % 2nat;
  assert(0nat <= r < 2nat);
  if r == 1nat {
    assert(2nat * (n / 2nat) + 1nat == n);
  } else {
    assert(r == 0nat);
    assert(2nat * (n / 2nat) + 0nat == n);
  }
}

/* helper modified by LLM (iteration 10): nat2bits correctness by induction */
proof fn lemma_nat2bits_correct(n: nat)
  ensures
    valid_bit_string(nat2bits(n)),
    str2int(nat2bits(n)) == n
  decreases n
{
  if n == 0nat {
    assert(valid_bit_string(seq!['0']));
    assert(str2int(seq!['0']) == 0nat);
  } else {
    lemma_nat2bits_correct(n / 2nat);
    let b: char = if n % 2nat == 1nat { '1' } else { '0' };

    // validity
    lemma_valid_concat(nat2bits(n / 2nat), b);
    assert(nat2bits(n) == nat2bits(n / 2nat) + seq![b]);
    assert(valid_bit_string(nat2bits(n)));

    // numeric correctness
    lemma_str2int_concat_char(nat2bits(n / 2nat), b);
    assert(str2int(nat2bits(n)) == str2int(nat2bits(n / 2nat) + seq![b]));
    assert(str2int(nat2bits(n / 2nat)) == n / 2nat);
    lemma_mod2_decomp(n);
    assert(2nat * (n / 2nat) + (if n % 2nat == 1nat { 1nat } else { 0nat }) == n);
    assert(str2int(nat2bits(n)) == n);
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
  /* code modified by LLM (iteration 10): construct result via Vec::from over spec bits sequence to avoid from_seq */
  proof {
      assert(str2int(s1@) >= str2int(s2@));
  }
  let ghost diff: int = str2int(s1@) - str2int(s2@);
  proof { assert(diff >= 0); }
  let ghost d: nat = diff as nat;
  proof {
      lemma_nat2bits_correct(d);
  }
  let res: Vec<char> = Vec::<char>::from(nat2bits(d));
  proof {
      assert(valid_bit_string(res@));
      assert(str2int(res@) == d);
      assert((d as int) == diff);
      assert(str2int(res@) == str2int(s1@) - str2int(s2@));
  }
  res
}
// </vc-code>


}

fn main() {}