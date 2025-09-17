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
proof fn lemma_str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires 
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        s1 != s2,
        exists |i: int| 0 <= i < s1.len() && s1[i] != s2[i] && 
            (forall |j: int| 0 <= j < i ==> s1[j] == s2[j])
    ensures 
        (exists |i: int| 0 <= i < s1.len() && s1[i] == '0' && s2[i] == '1' && 
            (forall |j: int| 0 <= j < i ==> s1[j] == s2[j])) ==> Str2Int(s1) < Str2Int(s2),
        (exists |i: int| 0 <= i < s1.len() && s1[i] == '1' && s2[i] == '0' && 
            (forall |j: int| 0 <= j < i ==> s1[j] == s2[j])) ==> Str2Int(s1) > Str2Int(s2)
{
    let diff_pos = choose |i: int| 0 <= i < s1.len() && s1[i] != s2[i] && 
        (forall |j: int| 0 <= j < i ==> s1[j] == s2[j]);
    
    lemma_str2int_prefix_equal(s1, s2, diff_pos);
    lemma_str2int_bit_difference(s1, s2, diff_pos);
}

proof fn lemma_str2int_prefix_equal(s1: Seq<char>, s2: Seq<char>, k: int)
    requires 
        ValidBitString(s1),
        ValidBitString(s2),
        0 <= k < s1.len(),
        k < s2.len(),
        forall |j: int| 0 <= j < k ==> s1[j] == s2[j]
    ensures 
        Str2Int(s1.subrange(0, k)) == Str2Int(s2.subrange(0, k))
    decreases k
{
    if k == 0 {
        assert(s1.subrange(0, 0).len() == 0);
        assert(s2.subrange(0, 0).len() == 0);
    } else {
        lemma_str2int_prefix_equal(s1, s2, k - 1);
        assert(s1[k-1] == s2[k-1]);
    }
}

proof fn lemma_str2int_bit_difference(s1: Seq<char>, s2: Seq<char>, k: int)
    requires 
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        0 <= k < s1.len(),
        forall |j: int| 0 <= j < k ==> s1[j] == s2[j],
        s1[k] != s2[k]
    ensures 
        s1[k] == '0' && s2[k] == '1' ==> Str2Int(s1) < Str2Int(s2),
        s1[k] == '1' && s2[k] == '0' ==> Str2Int(s1) > Str2Int(s2)
{
    let len = s1.len();
    let power = len - k - 1;
    
    lemma_str2int_prefix_equal(s1, s2, k);
    lemma_str2int_suffix_bound(s1.subrange(k+1, len as int));
    lemma_str2int_suffix_bound(s2.subrange(k+1, len as int));
    
    if s1[k] == '0' && s2[k] == '1' {
        assert(Str2Int(s1) < Str2Int(s2));
    } else if s1[k] == '1' && s2[k] == '0' {
        assert(Str2Int(s1) > Str2Int(s2));
    }
}

proof fn lemma_str2int_suffix_bound(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) < nat_pow(2, s.len())
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
    } else {
        lemma_str2int_suffix_bound(s.subrange(0, s.len() as int - 1));
        assert(Str2Int(s) < nat_pow(2, s.len()));
    }
}

spec fn nat_pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1 } else { base * nat_pow(base, exp - 1) }
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
    let len1 = s1.len();
    let len2 = s2.len();
    
    // First compare by length
    if len1 < len2 {
        proof {
            lemma_shorter_string_smaller(s1@, s2@);
        }
        return -1;
    } else if len1 > len2 {
        proof {
            lemma_shorter_string_smaller(s2@, s1@);
        }
        return 1;
    }
    
    // Same length, compare bit by bit from left to right
    let mut i = 0;
    while i < len1
        invariant 
            0 <= i <= len1,
            len1 == len2,
            ValidBitString(s1@),
            ValidBitString(s2@),
            forall |j: int| 0 <= j < i ==> s1@[j] == s2@[j]
    {
        if s1[i] < s2[i] {
            proof {
                assert(s1@[i as int] == '0' && s2@[i as int] == '1');
                lemma_str2int_monotonic(s1@, s2@);
            }
            return -1;
        } else if s1[i] > s2[i] {
            proof {
                assert(s1@[i as int] == '1' && s2@[i as int] == '0');
                lemma_str2int_monotonic(s1@, s2@);
            }
            return 1;
        }
        i += 1;
    }
    
    proof {
        assert(s1@ == s2@);
        lemma_equal_strings_equal_values(s1@, s2@);
    }
    return 0;
}
// </vc-code>

fn main() {}
}