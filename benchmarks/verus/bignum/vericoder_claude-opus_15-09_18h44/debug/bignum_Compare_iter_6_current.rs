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
    ensures Str2Int(seq![]) == 0
{
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
    assert(s.push('0').subrange(0, s.push('0').len() as int - 1) == s);
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
    assert(s.push('1').subrange(0, s.push('1').len() as int - 1) == s);
}

proof fn lemma_str2int_comparison(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
    ensures
        s1.len() == 0 && s2.len() == 0 ==> Str2Int(s1) == Str2Int(s2),
        s1.len() > 0 && s2.len() > 0 && s1.index(s1.len() as int - 1) == s2.index(s2.len() as int - 1) ==> 
            (Str2Int(s1.subrange(0, s1.len() as int - 1)) < Str2Int(s2.subrange(0, s2.len() as int - 1)) <==> Str2Int(s1) < Str2Int(s2)),
        s1.len() > 0 && s2.len() > 0 && s1.index(s1.len() as int - 1) == s2.index(s2.len() as int - 1) ==> 
            (Str2Int(s1.subrange(0, s1.len() as int - 1)) == Str2Int(s2.subrange(0, s2.len() as int - 1)) <==> Str2Int(s1) == Str2Int(s2)),
        s1.len() > 0 && s2.len() > 0 && s1.index(s1.len() as int - 1) == s2.index(s2.len() as int - 1) ==> 
            (Str2Int(s1.subrange(0, s1.len() as int - 1)) > Str2Int(s2.subrange(0, s2.len() as int - 1)) <==> Str2Int(s1) > Str2Int(s2)),
    decreases s1.len()
{
    if s1.len() == 0 {
    } else {
        let s1_prefix = s1.subrange(0, s1.len() as int - 1);
        let s2_prefix = s2.subrange(0, s2.len() as int - 1);
        assert(ValidBitString(s1_prefix));
        assert(ValidBitString(s2_prefix));
        if s1.len() > 1 {
            lemma_str2int_comparison(s1_prefix, s2_prefix);
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
    /* code modified by LLM (iteration 6): use usize for indexing slices in exec code */
    if s1.len() < s2.len() {
        return -1;
    } else if s1.len() > s2.len() {
        return 1;
    } else {
        let mut i: usize = 0;
        while i < s1.len()
            invariant
                i <= s1.len(),
                forall |j: int| 0 <= j && j < i as int ==> s1@[j] == s2@[j],
                Str2Int(s1@.subrange(0, i as int)) == Str2Int(s2@.subrange(0, i as int)),
        {
            if s1[i] == '1' && s2[i] == '0' {
                proof {
                    assert(s1@.subrange(0, i as int + 1) == s1@.subrange(0, i as int).push(s1@[i as int]));
                    assert(s2@.subrange(0, i as int + 1) == s2@.subrange(0, i as int).push(s2@[i as int]));
                    lemma_str2int_append_one(s1@.subrange(0, i as int));
                    lemma_str2int_append_zero(s2@.subrange(0, i as int));
                    assert(Str2Int(s1@.subrange(0, i as int + 1)) > Str2Int(s2@.subrange(0, i as int + 1)));
                }
                
                let mut j: usize = i + 1;
                while j < s1.len()
                    invariant
                        i < j,
                        j <= s1.len(),
                        Str2Int(s1@.subrange(0, i as int + 1)) > Str2Int(s2@.subrange(0, i as int + 1)),
                        Str2Int(s1@.subrange(0, j as int)) > Str2Int(s2@.subrange(0, j as int)),
                {
                    proof {
                        assert(s1@.subrange(0, j as int + 1) == s1@.subrange(0, j as int).push(s1@[j as int]));
                        assert(s2@.subrange(0, j as int + 1) == s2@.subrange(0, j as int).push(s2@[j as int]));
                        if s1@[j as int] == '0' {
                            lemma_str2int_append_zero(s1@.subrange(0, j as int));
                        } else {
                            lemma_str2int_append_one(s1@.subrange(0, j as int));
                        }
                        if s2@[j as int] == '0' {
                            lemma_str2int_append_zero(s2@.subrange(0, j as int));
                        } else {
                            lemma_str2int_append_one(s2@.subrange(0, j as int));
                        }
                    }
                    j = j + 1;
                }
                proof {
                    assert(s1@.subrange(0, s1.len() as int) == s1@);
                    assert(s2@.subrange(0, s2.len() as int) == s2@);
                }
                return 1;
            } else if s1[i] == '0' && s2[i] == '1' {
                proof {
                    assert(s1@.subrange(0, i as int + 1) == s1@.subrange(0, i as int).push(s1@[i as int]));
                    assert(s2@.subrange(0, i as int + 1) == s2@.subrange(0, i as int).push(s2@[i as int]));
                    lemma_str2int_append_zero(s1@.subrange(0, i as int));
                    lemma_str2int_append_one(s2@.subrange(0, i as int));
                    assert(Str2Int(s1@.subrange(0, i as int + 1)) < Str2Int(s2@.subrange(0, i as int + 1)));
                }
                
                let mut j: usize = i + 1;
                while j < s1.len()
                    invariant
                        i < j,
                        j <= s1.len(),
                        Str2Int(s1@.subrange(0, i as int + 1)) < Str2Int(s2@.subrange(0, i as int + 1)),
                        Str2Int(s1@.subrange(0, j as int)) < Str2Int(s2@.subrange(0, j as int)),
                {
                    proof {
                        assert(s1@.subrange(0, j as int + 1) == s1@.subrange(0, j as int).push(s1@[j as int]));
                        assert(s2@.subrange(0, j as int + 1) == s2@.subrange(0, j as int).push(s2@[j as int]));
                        if s1@[j as int] == '0' {
                            lemma_str2int_append_zero(s1@.subrange(0, j as int));
                        } else {
                            lemma_str2int_append_one(s1@.subrange(0, j as int));
                        }
                        if s2@[j as int] == '0' {
                            lemma_str2int_append_zero(s2@.subrange(0, j as int));
                        } else {
                            lemma_str2int_append_one(s2@.subrange(0, j as int));
                        }
                    }
                    j = j + 1;
                }
                proof {
                    assert(s1@.subrange(0, s1.len() as int) == s1@);
                    assert(s2@.subrange(0, s2.len() as int) == s2@);
                }
                return -1;
            } else {
                proof {
                    assert(s1@.subrange(0, i as int + 1) == s1@.subrange(0, i as int).push(s1@[i as int]));
                    assert(s2@.subrange(0, i as int + 1) == s2@.subrange(0, i as int).push(s2@[i as int]));
                    if s1@[i as int] == '0' {
                        lemma_str2int_append_zero(s1@.subrange(0, i as int));
                        lemma_str2int_append_zero(s2@.subrange(0, i as int));
                    } else {
                        lemma_str2int_append_one(s1@.subrange(0, i as int));
                        lemma_str2int_append_one(s2@.subrange(0, i as int));
                    }
                }
                i = i + 1;
            }
        }
        proof {
            assert(s1@.subrange(0, s1.len() as int) == s1@);
            assert(s2@.subrange(0, s2.len() as int) == s2@);
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


