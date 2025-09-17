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

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    let mut t: Vec<char> = Vec::new();
    let mut first_one_found = false;
    let mut num_leading_zeros: nat = 0;

    if s.len() == 0 {
        t.push('0');
        return t;
    }

    let mut i: int = 0;
    while i < s.len() as int
        invariant
            0 <= i && i <= s.len() as int,
            t@.len() <= i as nat,
            first_one_found ==> (forall |j: int| 0 <= j && j < t@.len() as int ==> t@[j] == s@[num_leading_zeros as int + j]),
            !first_one_found ==>
                (forall |j: int| 0 <= j && j < i as int ==> s@[j] == '0'),
                num_leading_zeros == i as nat,
            ValidBitString(s@),
            ValidBitString(t@),

        decreases s.len() as int - i
    {
        if s@[i] == '1' {
            first_one_found = true;
        }
        if first_one_found {
            t.push(s@[i]);
        } else {
            num_leading_zeros = num_leading_zeros + 1;
        }
        i = i + 1;
    }

    if !first_one_found {
        t.push('0');
    }
    t
}
// </vc-code>

// <vc-spec>
exec fn CompareUnequal(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
   s1@.len() > 0,
   (s1@.len() > 1 ==> s1@[0] != '0'),
   s2@.len() > 0,
   (s2@.len() > 1 ==> s2@[0] != '0'),
   s1@.len() > s2@.len(),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1
// </vc-spec>
// <vc-code>
{
    if s1.len() > s2.len() {
        return 1;
    } else if s1.len() < s2.len() {
        return -1;
    } else {
        let mut i: int = 0;
        while i < s1.len() as int
            invariant
                0 <= i && i <= s1.len() as int,
                ValidBitString(s1@),
                ValidBitString(s2@),
                s1@.len() == s2@.len(),
                forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
            decreases s1.len() as int - i
        {
            if s1@[i] > s2@[i] {
                return 1;
            } else if s1@[i] < s2@[i] {
                return -1;
            }
            i = i + 1;
        }
        return 0;
    }
}
// </vc-code>

// <vc-helpers>
proof fn lemma_str2int_prepend_zero(s_orig: Seq<char>)
    requires ValidBitString(s_orig),
        s_orig.len() > 0,
        s_orig@[0] == '0',
    ensures Str2Int(s_orig) == Str2Int(s_orig.subrange(1, s_orig.len()))
{
    if s_orig.len() <= 1 {
        assert(Str2Int(s_orig) == 0);
        assert(Str2Int(s_orig.subrange(1, s_orig.len())) == 0);
    } else {
        let s_prime = s_orig.subrange(1, s_orig.len());
        assert(s_prime.len() == s_orig.len() - 1);
        lemma_str2int_prepend_zero(s_prime);
    }
}

proof fn lemma_normalize_bit_string_equal_str2int(s: Seq<char>, t: Seq<char>)
    requires ValidBitString(s),
        ValidBitString(t),
        t.len() > 0,
        t.len() > 1 ==> t@[0] != '0',
        (forall |i: int| 0 <= i && i < s.len() ==> s@[i] == '0') ==> t.len() == 1 && t@[0] == '0',
        (exists |k: int| 0 <= k && k < s.len() && s@[k] == '1') ==> (
            exists |leading_zeros: int| 0 <= leading_zeros && leading_zeros < s.len() && (
                (forall |i: int| 0 <= i && i < leading_zeros ==> s@[i] == '0') &&
                s@[leading_zeros] == '1' &&
                t == s.subrange(leading_zeros, s.len())
            )
        ),
    ensures Str2Int(s) == Str2Int(t)
{
    if (forall |i: int| 0 <= i && i < s.len() ==> s@[i] == '0') {
        assert(Str2Int(s) == 0);
        assert(Str2Int(t) == 0);
    } else {
        let mut leading_zeros: int = 0;
        while leading_zeros < s.len() && s@[leading_zeros] == '0'
            invariant
                0 <= leading_zeros && leading_zeros <= s.len(),
                ValidBitString(s),
                (forall |i: int| 0 <= i && i < leading_zeros ==> s@[i] == '0'),
            decreases s.len() - leading_zeros
        {
            leading_zeros = leading_zeros + 1;
        }

        assert(s@[leading_zeros] == '1');
        assert(t == s.subrange(leading_zeros, s.len()));

        let mut current_s = s;
        let mut i = 0;

        while i < leading_zeros
            invariant
                0 <= i && i <= leading_zeros,
                ValidBitString(s),
                (forall |j: int| 0 <= j && j < i ==> s@[j] == '0'),
                Str2Int(s) == Str2Int(current_s),
                current_s == s.subrange(i, s.len()),
            decreases leading_zeros - i
        {
            assert(current_s.len() > 0);
            assert(current_s@[0] == '0');
            lemma_str2int_prepend_zero(current_s);
            current_s = current_s.subrange(1, current_s.len());
            i = i + 1;
        }
        assert(current_s == s.subrange(leading_zeros, s.len()));
        assert(Str2Int(s) == Str2Int(s.subrange(leading_zeros, s.len())));
        assert(Str2Int(s.subrange(leading_zeros, s.len())) == Str2Int(t));
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
    let s1_norm = NormalizeBitString(s1);
    let s2_norm = NormalizeBitString(s2);
    lemma_normalize_bit_string_equal_str2int(s1@, s1_norm@);
    lemma_normalize_bit_string_equal_str2int(s2@, s2_norm@);
    CompareUnequal(s1_norm.as_slice(), s2_norm.as_slice())
}
// </vc-code>

fn main() {}
}


