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
    assert(s.push('0').subrange(0, s.push('0').len() as int - 1) == s);
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
    assert(s.push('1').subrange(0, s.push('1').len() as int - 1) == s);
}

proof fn lemma_str2int_prefix_smaller(s: Seq<char>, c: char)
    requires ValidBitString(s),
        c == '0' || c == '1'
    ensures Str2Int(s) <= Str2Int(s.push(c))
{
    if c == '0' {
        lemma_str2int_append_zero(s);
    } else {
        lemma_str2int_append_one(s);
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
    /* code modified by LLM (iteration 4): Added decreases clause to while loop */
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
            decreases s2.len() - j
        {
            s2_suffix.push(s2[j]);
            j = j + 1;
        }
        return Compare(s1, &s2_suffix);
    } else if s1.len() > s2.len() {
        let mut i: usize = 0;
        while i < s1.len() - s2.len()
            invariant
                i <= s1.len() - s2.len(),
                forall |j: int| 0 <= j && j < i ==> s1@.index(j) == '0',
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
            decreases s1.len() - j
        {
            s1_suffix.push(s1[j]);
            j = j + 1;
        }
        return Compare(&s1_suffix, s2);
    } else {
        let mut i: usize = 0;
        while i < s1.len()
            invariant
                i <= s1.len(),
                s1@.len() == s2@.len(),
                forall |j: int| 0 <= j && j < i ==> s1@.index(j) == s2@.index(j),
            decreases s1.len() - i
        {
            if s1[i] < s2[i] {
                return -1;
            } else if s1[i] > s2[i] {
                return 1;
            }
            i = i + 1;
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


