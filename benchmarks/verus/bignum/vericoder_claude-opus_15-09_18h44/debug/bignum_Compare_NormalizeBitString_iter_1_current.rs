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
proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
    let s_new = s.push('0');
    assert(s_new.subrange(0, s_new.len() - 1) == s);
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
    let s_new = s.push('1');
    assert(s_new.subrange(0, s_new.len() - 1) == s);
}

proof fn lemma_str2int_comparison(s1: Seq<char>, s2: Seq<char>)
    requires 
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len()
    ensures
        s1.len() == 0 ==> Str2Int(s1) == Str2Int(s2),
        s1.len() > 0 && s1.subrange(0, s1.len() - 1) == s2.subrange(0, s2.len() - 1) ==> {
            (s1[s1.len() - 1] == s2[s2.len() - 1] ==> Str2Int(s1) == Str2Int(s2)) &&
            (s1[s1.len() - 1] == '0' && s2[s2.len() - 1] == '1' ==> Str2Int(s1) < Str2Int(s2)) &&
            (s1[s1.len() - 1] == '1' && s2[s2.len() - 1] == '0' ==> Str2Int(s1) > Str2Int(s2))
        }
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(s2.len() == 0);
        lemma_str2int_empty();
    } else {
        let s1_prefix = s1.subrange(0, s1.len() - 1);
        let s2_prefix = s2.subrange(0, s2.len() - 1);
        if s1_prefix == s2_prefix {
            let c1 = s1[s1.len() - 1];
            let c2 = s2[s2.len() - 1];
            assert(Str2Int(s1) == 2 * Str2Int(s1_prefix) + (if c1 == '1' { 1 } else { 0 }));
            assert(Str2Int(s2) == 2 * Str2Int(s2_prefix) + (if c2 == '1' { 1 } else { 0 }));
        }
    }
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
    if s1.len() == 0 && s2.len() == 0 {
        proof {
            lemma_str2int_empty();
        }
        return 0;
    } else if s1.len() == 0 {
        proof {
            lemma_str2int_empty();
            assert(Str2Int(s1@) == 0);
            assert(s2@.len() > 0);
            if s2@.len() == 1 {
                if s2[0] == '1' {
                    assert(Str2Int(s2@) == 1);
                } else {
                    assert(Str2Int(s2@) == 0);
                }
            }
            assert(Str2Int(s2@) >= 0);
        }
        return -1;
    } else if s2.len() == 0 {
        proof {
            lemma_str2int_empty();
            assert(Str2Int(s2@) == 0);
            assert(s1@.len() > 0);
            assert(Str2Int(s1@) >= 0);
        }
        return 1;
    } else if s1.len() < s2.len() {
        return -1;
    } else if s1.len() > s2.len() {
        return 1;
    } else {
        let mut i: usize = 0;
        while i < s1.len()
            invariant
                0 <= i <= s1.len(),
                s1@.len() == s2@.len(),
                forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j]
        {
            if s1[i] != s2[i] {
                if s1[i] == '0' && s2[i] == '1' {
                    proof {
                        lemma_str2int_comparison(s1@, s2@);
                    }
                    return -1;
                } else {
                    proof {
                        lemma_str2int_comparison(s1@, s2@);
                    }
                    return 1;
                }
            }
            i = i + 1;
        }
        proof {
            assert(forall |j: int| 0 <= j && j < s1@.len() ==> s1@[j] == s2@[j]);
            assert(s1@ =~= s2@);
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


