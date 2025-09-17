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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added power function and fixed compilation errors */
spec fn pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow(base, exp - 1)
    }
}

proof fn lemma_str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        s1.len() > 0,
        forall |i: int| 0 <= i < s1.len() as int - 1 ==> s1.index(i) == s2.index(i),
        s1.index(s1.len() as int - 1) == '0',
        s2.index(s2.len() as int - 1) == '1'
    ensures
        Str2Int(s1) < Str2Int(s2)
{
    assert(s1.len() > 0);
    let prefix1 = s1.subrange(0, s1.len() as int - 1);
    let prefix2 = s2.subrange(0, s2.len() as int - 1);
    assert(prefix1 == prefix2);
    assert(Str2Int(prefix1) == Str2Int(prefix2));
    assert(Str2Int(s1) == 2 * Str2Int(prefix1) + 0);
    assert(Str2Int(s2) == 2 * Str2Int(prefix2) + 1);
}

proof fn lemma_str2int_equal(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1 == s2
    ensures
        Str2Int(s1) == Str2Int(s2)
{
}

proof fn lemma_length_comparison(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > s2.len(),
        s2.len() > 0
    ensures
        Str2Int(s1) > Str2Int(s2)
{
    assert(Str2Int(s1) >= pow(2nat, s2.len() as nat));
    assert(Str2Int(s2) < pow(2nat, s2.len() as nat));
}

proof fn lemma_first_difference(s1: Seq<char>, s2: Seq<char>, pos: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        s1.len() > 0,
        0 <= pos < s1.len(),
        forall |i: int| 0 <= i < pos ==> s1.index(i) == s2.index(i),
        s1.index(pos) == '1',
        s2.index(pos) == '0'
    ensures
        Str2Int(s1) > Str2Int(s2)
{
}
// </vc-helpers>

// <vc-spec>
exec fn Compare(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1,
  decreases Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation errors and added proper proof calls */
    if s1.len() == 0 && s2.len() == 0 {
        proof {
            lemma_str2int_equal(s1@, s2@);
        }
        return 0;
    }
    
    if s1.len() < s2.len() {
        if s2.len() > 0 {
            proof {
                lemma_length_comparison(s2@, s1@);
            }
        }
        return -1;
    }
    
    if s1.len() > s2.len() {
        if s1.len() > 0 {
            proof {
                lemma_length_comparison(s1@, s2@);
            }
        }
        return 1;
    }
    
    // Same length case
    let mut i = 0;
    while i < s1.len()
        invariant
            i <= s1.len(),
            s1.len() == s2.len(),
            forall |j: int| 0 <= j < i ==> s1[j] == s2[j]
        decreases s1.len() - i
    {
        if s1[i] == '0' && s2[i] == '1' {
            proof {
                assert(s1.len() > 0);
                lemma_str2int_monotonic(s1@, s2@);
            }
            return -1;
        }
        if s1[i] == '1' && s2[i] == '0' {
            proof {
                lemma_first_difference(s1@, s2@, i as int);
            }
            return 1;
        }
        i += 1;
    }
    
    proof {
        lemma_str2int_equal(s1@, s2@);
    }
    return 0;
}
// </vc-code>

fn main() {}
}


