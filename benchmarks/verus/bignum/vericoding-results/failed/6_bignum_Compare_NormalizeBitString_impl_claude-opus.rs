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
/* helper modified by LLM (iteration 10): Fixed lemma proofs and added helper function for Str2Int computation */
proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_single(c: char)
    requires c == '0' || c == '1'
    ensures 
        c == '0' ==> Str2Int(seq![c]) == 0,
        c == '1' ==> Str2Int(seq![c]) == 1
{
    let s = seq![c];
    assert(s.len() == 1);
    assert(s.subrange(0, 0) == Seq::<char>::empty());
    lemma_str2int_empty();
    assert(Str2Int(s.subrange(0, 0)) == 0);
    assert(s[0] == c);
}

proof fn lemma_str2int_positive(s: Seq<char>)
    requires 
        ValidBitString(s),
        s.len() > 0
    ensures
        (exists |i: int| 0 <= i && i < s.len() && s[i] == '1') ==> Str2Int(s) > 0,
        (forall |i: int| 0 <= i && i < s.len() ==> s[i] == '0') ==> Str2Int(s) == 0
    decreases s.len()
{
    if s.len() == 1 {
        lemma_str2int_single(s[0]);
        if s[0] == '1' {
            assert(Str2Int(s) == 1);
            assert(Str2Int(s) > 0);
        } else {
            assert(s[0] == '0');
            assert(Str2Int(s) == 0);
        }
    } else {
        let prefix = s.subrange(0, s.len() - 1);
        let last = s[s.len() - 1];
        assert(ValidBitString(prefix));
        lemma_str2int_positive(prefix);
        
        if last == '1' {
            assert(Str2Int(s) == 2 * Str2Int(prefix) + 1);
            assert(Str2Int(s) >= 1);
            assert(Str2Int(s) > 0);
        } else {
            assert(last == '0');
            assert(Str2Int(s) == 2 * Str2Int(prefix));
            
            if exists |i: int| 0 <= i && i < s.len() && s[i] == '1' {
                assert(exists |j: int| 0 <= j && j < prefix.len() && prefix[j] == '1');
                assert(Str2Int(prefix) > 0);
                assert(Str2Int(s) == 2 * Str2Int(prefix));
                assert(Str2Int(s) > 0);
            } else {
                assert(forall |i: int| 0 <= i && i < s.len() ==> s[i] == '0');
                assert(forall |j: int| 0 <= j && j < prefix.len() ==> prefix[j] == '0');
                assert(Str2Int(prefix) == 0);
                assert(Str2Int(s) == 0);
            }
        }
    }
}

proof fn lemma_str2int_lexicographic(s1: Seq<char>, s2: Seq<char>, i: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        0 <= i < s1.len(),
        forall |j: int| 0 <= j && j < i ==> s1[j] == s2[j],
        s1[i] == '0',
        s2[i] == '1'
    ensures Str2Int(s1) < Str2Int(s2)
    decreases s1.len()
{
    if s1.len() == 1 {
        assert(i == 0);
        lemma_str2int_single(s1[0]);
        lemma_str2int_single(s2[0]);
        assert(Str2Int(s1) == 0);
        assert(Str2Int(s2) == 1);
    } else {
        let s1_prefix = s1.subrange(0, s1.len() - 1);
        let s2_prefix = s2.subrange(0, s2.len() - 1);
        let s1_last = s1[s1.len() - 1];
        let s2_last = s2[s2.len() - 1];
        
        if i == s1.len() - 1 {
            assert(forall |j: int| 0 <= j && j < s1_prefix.len() ==> s1_prefix[j] == s2_prefix[j]);
            assert(s1_prefix =~= s2_prefix);
            assert(Str2Int(s1_prefix) == Str2Int(s2_prefix));
            assert(s1_last == '0' && s2_last == '1');
            assert(Str2Int(s1) == 2 * Str2Int(s1_prefix));
            assert(Str2Int(s2) == 2 * Str2Int(s2_prefix) + 1);
            assert(Str2Int(s1) < Str2Int(s2));
        } else {
            assert(i < s1_prefix.len());
            assert(ValidBitString(s1_prefix));
            assert(ValidBitString(s2_prefix));
            assert(s1_prefix[i] == s1[i]);
            assert(s2_prefix[i] == s2[i]);
            lemma_str2int_lexicographic(s1_prefix, s2_prefix, i);
            assert(Str2Int(s1_prefix) < Str2Int(s2_prefix));
            assert(Str2Int(s1) == 2 * Str2Int(s1_prefix) + if s1_last == '1' { 1nat } else { 0nat });
            assert(Str2Int(s2) == 2 * Str2Int(s2_prefix) + if s2_last == '1' { 1nat } else { 0nat });
            assert(Str2Int(s1) < Str2Int(s2));
        }
    }
}

exec fn compute_str2int(s: &[char]) -> (result: u64)
    requires 
        ValidBitString(s@),
        s@.len() <= 64,
    ensures result == Str2Int(s@)
{
    let mut val: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            val == Str2Int(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        val = val * 2;
        if s[i] == '1' {
            val = val + 1;
        }
        i = i + 1;
    }
    assert(s@.subrange(0, s@.len() as int) =~= s@);
    val
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
    /* code modified by LLM (iteration 10): Use exec function to compute Str2Int values and compare them */
    if s1.len() > 64 || s2.len() > 64 {
        // Fall back to lexicographic comparison for very long strings
        if s1.len() < s2.len() {
            // Check if s1 is all zeros
            let mut all_zeros = true;
            let mut j: usize = 0;
            while j < s1.len()
                invariant
                    0 <= j <= s1.len(),
                    all_zeros <==> (forall |k: int| 0 <= k && k < j ==> s1@[k] == '0'),
                decreases s1.len() - j
            {
                if s1[j] == '1' {
                    all_zeros = false;
                    break;
                }
                j = j + 1;
            }
            if all_zeros {
                // Check if s2 is also all zeros
                let mut s2_all_zeros = true;
                let mut k: usize = 0;
                while k < s2.len()
                    invariant
                        0 <= k <= s2.len(),
                        s2_all_zeros <==> (forall |m: int| 0 <= m && m < k ==> s2@[m] == '0'),
                    decreases s2.len() - k
                {
                    if s2[k] == '1' {
                        s2_all_zeros = false;
                        break;
                    }
                    k = k + 1;
                }
                if s2_all_zeros {
                    proof {
                        lemma_str2int_positive(s1@);
                        lemma_str2int_positive(s2@);
                    }
                    return 0;
                } else {
                    return -1;
                }
            } else {
                return -1;
            }
        } else if s1.len() > s2.len() {
            // Check if s2 is all zeros
            let mut all_zeros = true;
            let mut j: usize = 0;
            while j < s2.len()
                invariant
                    0 <= j <= s2.len(),
                    all_zeros <==> (forall |k: int| 0 <= k && k < j ==> s2@[k] == '0'),
                decreases s2.len() - j
            {
                if s2[j] == '1' {
                    all_zeros = false;
                    break;
                }
                j = j + 1;
            }
            if all_zeros {
                // Check if s1 is also all zeros
                let mut s1_all_zeros = true;
                let mut k: usize = 0;
                while k < s1.len()
                    invariant
                        0 <= k <= s1.len(),
                        s1_all_zeros <==> (forall |m: int| 0 <= m && m < k ==> s1@[m] == '0'),
                    decreases s1.len() - k
                {
                    if s1[k] == '1' {
                        s1_all_zeros = false;
                        break;
                    }
                    k = k + 1;
                }
                if s1_all_zeros {
                    proof {
                        lemma_str2int_positive(s1@);
                        lemma_str2int_positive(s2@);
                    }
                    return 0;
                } else {
                    return 1;
                }
            } else {
                return 1;
            }
        } else {
            // Same length - compare lexicographically
            let mut i: usize = 0;
            while i < s1.len()
                invariant
                    0 <= i <= s1.len(),
                    s1@.len() == s2@.len(),
                    forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
                decreases s1.len() - i
            {
                if s1[i] != s2[i] {
                    if s1[i] == '0' && s2[i] == '1' {
                        proof {
                            lemma_str2int_lexicographic(s1@, s2@, i as int);
                        }
                        return -1;
                    } else {
                        proof {
                            lemma_str2int_lexicographic(s2@, s1@, i as int);
                        }
                        return 1;
                    }
                }
                i = i + 1;
            }
            proof {
                assert(s1@ =~= s2@);
            }
            return 0;
        }
    } else {
        // Use exec function to compute values
        let val1 = compute_str2int(s1);
        let val2 = compute_str2int(s2);
        
        if val1 < val2 {
            return -1;
        } else if val1 == val2 {
            return 0;
        } else {
            return 1;
        }
    }
}
// </vc-code>

fn main() {}
}


