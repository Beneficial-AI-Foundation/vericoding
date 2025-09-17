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

proof fn lemma_str2int_append_0(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
    assert(s.push('0').subrange(0, s.push('0').len() as int - 1) == s);
}

proof fn lemma_str2int_append_1(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
    assert(s.push('1').subrange(0, s.push('1').len() as int - 1) == s);
}

proof fn lemma_str2int_compare_same_len(s1: Seq<char>, s2: Seq<char>, i: int)
    requires 
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        0 <= i <= s1.len(),
        forall |j: int| 0 <= j < i ==> s1[j] == s2[j],
        i < s1.len() ==> s1[i] != s2[i]
    ensures
        i == s1.len() ==> Str2Int(s1) == Str2Int(s2),
        i < s1.len() && s1[i] == '0' && s2[i] == '1' ==> Str2Int(s1) < Str2Int(s2),
        i < s1.len() && s1[i] == '1' && s2[i] == '0' ==> Str2Int(s1) > Str2Int(s2)
    decreases s1.len() - i
{
    if i == s1.len() {
        assert(s1 =~= s2);
    } else if i == s1.len() - 1 {
        assert(s1.subrange(0, s1.len() - 1) =~= s2.subrange(0, s2.len() - 1));
    } else {
        lemma_str2int_compare_same_len(s1.subrange(0, s1.len() - 1), s2.subrange(0, s2.len() - 1), i);
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
    /* code modified by LLM (iteration 3): Added decreases clauses to all while loops */
    if s1.len() < s2.len() {
        let mut j = 0;
        while j < s2.len() - s1.len()
            invariant
                0 <= j,
                j <= s2.len() - s1.len(),
                forall |k: int| 0 <= k < j ==> s2@[k] == '0'
            decreases s2.len() - s1.len() - j
        {
            if s2[j] == '1' {
                return -1;
            }
            j = j + 1;
        }
        let mut i = 0;
        while i < s1.len()
            invariant
                0 <= i,
                i <= s1.len(),
                forall |k: int| 0 <= k < i ==> s1@[k] == s2@[s2.len() - s1.len() + k]
            decreases s1.len() - i
        {
            if s1[i] < s2[s2.len() - s1.len() + i] {
                proof { lemma_str2int_compare_same_len(s1@, s2@.subrange((s2@.len() - s1@.len()) as int, s2@.len() as int), i as int); }
                return -1;
            } else if s1[i] > s2[s2.len() - s1.len() + i] {
                proof { lemma_str2int_compare_same_len(s1@, s2@.subrange((s2@.len() - s1@.len()) as int, s2@.len() as int), i as int); }
                return 1;
            }
            i = i + 1;
        }
        proof { lemma_str2int_compare_same_len(s1@, s2@.subrange((s2@.len() - s1@.len()) as int, s2@.len() as int), s1@.len() as int); }
        return 0;
    } else if s1.len() > s2.len() {
        let mut j = 0;
        while j < s1.len() - s2.len()
            invariant
                0 <= j,
                j <= s1.len() - s2.len(),
                forall |k: int| 0 <= k < j ==> s1@[k] == '0'
            decreases s1.len() - s2.len() - j
        {
            if s1[j] == '1' {
                return 1;
            }
            j = j + 1;
        }
        let mut i = 0;
        while i < s2.len()
            invariant
                0 <= i,
                i <= s2.len(),
                forall |k: int| 0 <= k < i ==> s1@[s1.len() - s2.len() + k] == s2@[k]
            decreases s2.len() - i
        {
            if s1[s1.len() - s2.len() + i] < s2[i] {
                proof { lemma_str2int_compare_same_len(s1@.subrange((s1@.len() - s2@.len()) as int, s1@.len() as int), s2@, i as int); }
                return -1;
            } else if s1[s1.len() - s2.len() + i] > s2[i] {
                proof { lemma_str2int_compare_same_len(s1@.subrange((s1@.len() - s2@.len()) as int, s1@.len() as int), s2@, i as int); }
                return 1;
            }
            i = i + 1;
        }
        proof { lemma_str2int_compare_same_len(s1@.subrange((s1@.len() - s2@.len()) as int, s1@.len() as int), s2@, s2@.len() as int); }
        return 0;
    } else {
        let mut i = 0;
        while i < s1.len()
            invariant
                0 <= i,
                i <= s1.len(),
                forall |k: int| 0 <= k < i ==> s1@[k] == s2@[k]
            decreases s1.len() - i
        {
            if s1[i] < s2[i] {
                proof { lemma_str2int_compare_same_len(s1@, s2@, i as int); }
                return -1;
            } else if s1[i] > s2[i] {
                proof { lemma_str2int_compare_same_len(s1@, s2@, i as int); }
                return 1;
            }
            i = i + 1;
        }
        proof { lemma_str2int_compare_same_len(s1@, s2@, s1@.len() as int); }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


