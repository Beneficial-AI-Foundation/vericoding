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
/* helper modified by LLM (iteration 7): fixed type mismatch by casting nat to int for subrange calls */
proof fn str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        s1.len() > 0,
        exists |i: int| 0 <= i < s1.len() && s1.index(i) == '0' && s2.index(i) == '1' && forall |j: int| 0 <= j < i ==> s1.index(j) == s2.index(j)
    ensures
        Str2Int(s1) < Str2Int(s2)
    decreases s1.len()
{
    let first_diff = choose |i: int| 0 <= i < s1.len() && s1.index(i) == '0' && s2.index(i) == '1' && forall |j: int| 0 <= j < i ==> s1.index(j) == s2.index(j);
    
    if first_diff == s1.len() - 1 {
        assert(s1.subrange(0, s1.len() - 1) == s2.subrange(0, s2.len() - 1));
        assert(Str2Int(s1) == 2 * Str2Int(s1.subrange(0, s1.len() - 1)));
        assert(Str2Int(s2) == 2 * Str2Int(s2.subrange(0, s2.len() - 1)) + 1);
    } else {
        str2int_monotonic(s1.subrange(first_diff, s1.len() as int), s2.subrange(first_diff, s2.len() as int));
    }
}

proof fn str2int_length_property(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() < s2.len(),
        s2.len() > 0
    ensures
        Str2Int(s1) < Str2Int(s2)
    decreases s2.len()
{
    str2int_upper_bound(s1);
    if s2.index(0) == '1' {
        str2int_lower_bound(s2);
    } else {
        str2int_positive(s2);
    }
}

proof fn str2int_upper_bound(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < pow(2nat, s.len() as nat)
    decreases s.len()
{
    if s.len() == 0 {
        // Base case
    } else if s.len() == 1 {
        assert(pow(2nat, 1nat) == 2);
    } else {
        str2int_upper_bound(s.subrange(0, s.len() - 1));
    }
}

proof fn str2int_lower_bound(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0, s.index(0) == '1'
    ensures Str2Int(s) >= pow(2nat, (s.len() - 1) as nat)
    decreases s.len()
{
    if s.len() == 1 {
        assert(pow(2nat, 0nat) == 1);
    } else {
        let prefix = s.subrange(0, s.len() - 1);
        if prefix.len() > 0 && prefix.index(0) == '1' {
            str2int_lower_bound(prefix);
        }
    }
}

proof fn str2int_positive(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) >= 1 || (forall |i: int| 0 <= i < s.len() ==> s.index(i) == '0')
    decreases s.len()
{
    if s.len() == 1 {
        // Base case is trivial
    } else {
        if s.index(s.len() - 1) == '1' {
            assert(Str2Int(s) >= 1);
        } else {
            str2int_positive(s.subrange(0, s.len() - 1));
        }
    }
}

proof fn str2int_equal_iff_seq_equal(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len()
    ensures
        Str2Int(s1) == Str2Int(s2) <==> s1 == s2
    decreases s1.len()
{
    if s1.len() == 0 {
        // Base case
    } else {
        if s1 != s2 {
            let last1 = s1.index(s1.len() - 1);
            let last2 = s2.index(s2.len() - 1);
            let prefix1 = s1.subrange(0, s1.len() - 1);
            let prefix2 = s2.subrange(0, s2.len() - 1);
            
            if last1 != last2 {
                // Different last characters means different Str2Int
            } else {
                str2int_equal_iff_seq_equal(prefix1, prefix2);
            }
        }
    }
}

spec fn pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1 } else { base * pow(base, (exp - 1) as nat) }
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
/* code modified by LLM (iteration 7): fixed type mismatch - no changes needed in code body */
{
    if s1.len() != s2.len() {
        if s1.len() < s2.len() {
            proof {
                if s2.len() > 0 {
                    str2int_length_property(s1@, s2@);
                }
            }
            return -1;
        } else {
            proof {
                if s1.len() > 0 {
                    str2int_length_property(s2@, s1@);
                }
            }
            return 1;
        }
    }
    
    let mut i = 0;
    while i < s1.len()
        invariant
            i <= s1.len(),
            s1.len() == s2.len(),
            ValidBitString(s1@),
            ValidBitString(s2@),
            forall |j: int| 0 <= j < i ==> s1@.index(j) == s2@.index(j),
        decreases s1.len() - i
    {
        if s1[i] != s2[i] {
            if s1[i] == '0' && s2[i] == '1' {
                proof {
                    if s1@.len() > 0 {
                        assert(exists |k: int| 0 <= k < s1@.len() && s1@.index(k) == '0' && s2@.index(k) == '1' && forall |j: int| 0 <= j < k ==> s1@.index(j) == s2@.index(j));
                        str2int_monotonic(s1@, s2@);
                    }
                }
                return -1;
            } else {
                proof {
                    if s2@.len() > 0 {
                        assert(exists |k: int| 0 <= k < s2@.len() && s2@.index(k) == '0' && s1@.index(k) == '1' && forall |j: int| 0 <= j < k ==> s2@.index(j) == s1@.index(j));
                        str2int_monotonic(s2@, s1@);
                    }
                }
                return 1;
            }
        }
        i += 1;
    }
    
    proof {
        assert(s1@ == s2@);
        if s1@.len() == s2@.len() {
            str2int_equal_iff_seq_equal(s1@, s2@);
        }
    }
    return 0;
}
// </vc-code>

fn main() {}
}


