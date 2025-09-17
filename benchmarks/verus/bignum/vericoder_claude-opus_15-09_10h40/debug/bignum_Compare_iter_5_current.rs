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
/* helper modified by LLM (iteration 5): Added lemmas for reasoning about Str2Int and equal-length strings */
proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_leading_zeros(s1: Seq<char>, s2: Seq<char>, n: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        0 <= n <= s1.len(),
        n <= s2.len(),
        forall |i: int| 0 <= i && i < n ==> s1.index(i) == '0',
        forall |i: int| 0 <= i && i < n ==> s2.index(i) == '0',
        s1.subrange(n, s1.len() as int) == s2.subrange(n, s2.len() as int),
    ensures Str2Int(s1) == Str2Int(s2)
    decreases s1.len()
{
    if n == 0 {
        assert(s1 == s2);
    } else if s1.len() == 0 {
        assert(s2.len() == 0);
    } else {
        let s1_tail = s1.subrange(0, s1.len() as int - 1);
        let s2_tail = s2.subrange(0, s2.len() as int - 1);
        assert(s1.index(s1.len() as int - 1) == s2.index(s2.len() as int - 1));
        if s1.len() as int - 1 < n {
            assert(s1_tail.subrange(n, s1_tail.len() as int) == s2_tail.subrange(n, s2_tail.len() as int));
        }
        lemma_str2int_leading_zeros(s1_tail, s2_tail, if n <= s1.len() as int - 1 { n } else { s1.len() as int - 1 });
    }
}

proof fn lemma_str2int_compare_equal_length(s1: Seq<char>, s2: Seq<char>, i: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        0 <= i < s1.len(),
        forall |j: int| 0 <= j && j < i ==> s1.index(j) == s2.index(j),
        s1.index(i) != s2.index(i),
    ensures
        (s1.index(i) == '0' && s2.index(i) == '1') ==> Str2Int(s1) < Str2Int(s2),
        (s1.index(i) == '1' && s2.index(i) == '0') ==> Str2Int(s1) > Str2Int(s2),
    decreases s1.len()
{
    if s1.len() == 1 {
        assert(i == 0);
    } else {
        let s1_tail = s1.subrange(0, s1.len() as int - 1);
        let s2_tail = s2.subrange(0, s2.len() as int - 1);
        if i < s1.len() as int - 1 {
            lemma_str2int_compare_equal_length(s1_tail, s2_tail, i);
        } else {
            assert(i == s1.len() as int - 1);
            assert(s1_tail == s2_tail);
        }
    }
}

proof fn lemma_str2int_suffix_equal(s1: Seq<char>, s2: Seq<char>, start: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        0 <= start <= s1.len(),
        0 <= start <= s2.len(),
        s1.subrange(start, s1.len() as int) == s2.subrange(start, s2.len() as int),
        forall |i: int| 0 <= i && i < start ==> s1.index(i) == '0',
        forall |i: int| 0 <= i && i < start ==> s2.index(i) == '0',
    ensures Str2Int(s1) == Str2Int(s2)
{
    lemma_str2int_leading_zeros(s1, s2, start);
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
/* code modified by LLM (iteration 5): Fixed logic for comparison and added proof assertions */
{
    if s1.len() == 0 && s2.len() == 0 {
        proof { lemma_str2int_empty(); }
        return 0;
    } else if s1.len() == 0 {
        proof { lemma_str2int_empty(); }
        return -1;
    } else if s2.len() == 0 {
        proof { lemma_str2int_empty(); }
        return 1;
    } else if s1.len() < s2.len() {
        let mut i: usize = 0;
        while i < s2.len() - s1.len()
            invariant
                i <= s2.len() - s1.len(),
                forall |j: int| 0 <= j && j < i ==> s2@.index(j) == '0',
                ValidBitString(s2@),
            decreases (s2.len() - s1.len()) - i
        {
            if s2[i] == '1' {
                return -1;
            }
            i = i + 1;
        }
        let start_idx: usize = s2.len() - s1.len();
        let mut s2_suffix: Vec<char> = Vec::new();
        let mut j: usize = start_idx;
        while j < s2.len()
            invariant
                start_idx <= j <= s2.len(),
                s2_suffix@.len() == j - start_idx,
                forall |k: int| 0 <= k && k < s2_suffix@.len() ==> s2_suffix@.index(k) == s2@.index(start_idx as int + k),
                ValidBitString(s2_suffix@),
            decreases s2.len() - j
        {
            s2_suffix.push(s2[j]);
            j = j + 1;
        }
        proof {
            assert(s2_suffix@.len() == s1@.len());
            assert(forall |k: int| 0 <= k && k < start_idx ==> s2@.index(k) == '0');
            lemma_str2int_suffix_equal(s2@, s2@.subrange(0, start_idx as int) + s2_suffix@, start_idx as int);
        }
        return Compare(s1, &s2_suffix);
    } else if s1.len() > s2.len() {
        let mut i: usize = 0;
        while i < s1.len() - s2.len()
            invariant
                i <= s1.len() - s2.len(),
                forall |j: int| 0 <= j && j < i ==> s1@.index(j) == '0',
                ValidBitString(s1@),
            decreases (s1.len() - s2.len()) - i
        {
            if s1[i] == '1' {
                return 1;
            }
            i = i + 1;
        }
        let start_idx: usize = s1.len() - s2.len();
        let mut s1_suffix: Vec<char> = Vec::new();
        let mut j: usize = start_idx;
        while j < s1.len()
            invariant
                start_idx <= j <= s1.len(),
                s1_suffix@.len() == j - start_idx,
                forall |k: int| 0 <= k && k < s1_suffix@.len() ==> s1_suffix@.index(k) == s1@.index(start_idx as int + k),
                ValidBitString(s1_suffix@),
            decreases s1.len() - j
        {
            s1_suffix.push(s1[j]);
            j = j + 1;
        }
        proof {
            assert(s1_suffix@.len() == s2@.len());
            assert(forall |k: int| 0 <= k && k < start_idx ==> s1@.index(k) == '0');
            lemma_str2int_suffix_equal(s1@, s1@.subrange(0, start_idx as int) + s1_suffix@, start_idx as int);
        }
        return Compare(&s1_suffix, s2);
    } else {
        let mut i: usize = 0;
        while i < s1.len()
            invariant
                i <= s1.len(),
                s1@.len() == s2@.len(),
                forall |j: int| 0 <= j && j < i ==> s1@.index(j) == s2@.index(j),
                ValidBitString(s1@),
                ValidBitString(s2@),
            decreases s1.len() - i
        {
            if s1[i] < s2[i] {
                proof {
                    assert(s1@.index(i as int) == '0' && s2@.index(i as int) == '1');
                    lemma_str2int_compare_equal_length(s1@, s2@, i as int);
                }
                return -1;
            } else if s1[i] > s2[i] {
                proof {
                    assert(s1@.index(i as int) == '1' && s2@.index(i as int) == '0');
                    lemma_str2int_compare_equal_length(s1@, s2@, i as int);
                }
                return 1;
            }
            i = i + 1;
        }
        assert(forall |j: int| 0 <= j && j < s1@.len() ==> s1@.index(j) == s2@.index(j));
        assert(s1@ == s2@);
        return 0;
    }
}
// </vc-code>

fn main() {}
}


