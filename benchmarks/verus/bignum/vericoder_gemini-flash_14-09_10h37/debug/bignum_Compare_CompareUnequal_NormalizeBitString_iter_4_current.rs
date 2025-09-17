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
/* code modified by LLM (iteration 4): Fix type errors related to usize/int and sequence indexing. */
{
    let mut t: Vec<char> = Vec::new();
    let mut i: int = 0; // Changed to int
    while i < s.len() as int && s.view_at(i as nat) == '0' // Use view_at and cast i to nat
        invariant
            0 <= i,
            i <= s.len() as int,
            t@.len() == 0,
            forall |j: int| 0 <= j && j < i ==> s@.view_at(j as nat) == '0',
        decreases (s.len() as int) - i
    {
        i = i + 1;
    }

    if i == s.len() as int {
        t.push('0');
    } else {
        let start_index: int = i;
        while i < s.len() as int
            invariant
                start_index <= i,
                i <= s.len() as int,
                t@.len() == (i - start_index) as nat,
                forall |k: int| start_index <= k && k < i ==> t@.view_at((k - start_index) as nat) == s@.view_at(k as nat),
                ValidBitString(s@),
                ValidBitString(t@),
            decreases (s.len() as int) - i
        {
            t.push(s.view_at(i as nat)); // Use view_at and cast i to nat
            i = i + 1;
        }
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
/* code modified by LLM (iteration 4): Fix type errors related to usize/int and sequence indexing, and change for loop to while. */
{
    if s1@.len() > s2@.len() {
        proof {
            reveal_Str2Int_non_zero_leading_digit();
            Str2Int_inequality_by_length(s1@, s2@);
        }
        1
    } else if s1@.len() < s2@.len() {
        proof {
            reveal_Str2Int_non_zero_leading_digit();
            Str2Int_inequality_by_length(s2@, s1@);
        }
        -1
    } else {
        let mut i: int = 0; // Changed to int
        while i < s1@.len()
            invariant
                0 <= i,
                i <= s1@.len(),
                s1@.len() == s2@.len(),
                ValidBitString(s1@),
                ValidBitString(s2@),
                forall |j: int| 0 <= j && j < i ==> s1@.view_at(j as nat) == s2@.view_at(j as nat),
            decreases (s1@.len()) - i
        {
            if s1@.view_at(i as nat) != s2@.view_at(i as nat) { // Use view_at and cast i to nat
                break;
            }
            i = i + 1;
        }

        if i == s1@.len() {
            0
        } else if s1@.view_at(i as nat) == '1' { // Use view_at and cast i to nat
            proof {
                Str2Int_inequality_by_first_diff(s1@, s2@, i);
            }
            1
        } else {
            proof {
                Str2Int_inequality_by_first_diff(s2@, s1@, i);
            }
            -1
        }
    }
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed issues with `s@[0]` and `s.subrange(0, (s.len() - 1) as int).len() > 0 && s@[0] == '1'` by using `s.view_at(0 as nat)` and `s.subrange(0, (s.len() - 1) as nat).len() > 0 && s.view_at(0 as nat) == '1'` respectively. Also, replaced `1u64 << len_short` with `2u64.pow(len_short as u32)` for type correctness and consistency. Similar replacements for `len_long`. */
proof fn reveal_Str2Int_non_zero_leading_digit()
{
    assert forall |s: Seq<char>| ValidBitString(s) && s.len() > 0 && s.view_at(0 as nat) == '1' implies Str2Int(s) > 0 by {
        if s.len() == 1 {
            assert(Str2Int(s) == 1);
        } else {
            assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
            if s.subrange(0, (s.len() - 1) as int).len() > 0 && s.view_at(0 as nat) == '1' {
                reveal_Str2Int_non_zero_leading_digit();
            }
            assert(Str2Int(s) >= 1);
        }
    }
}

proof fn Str2Int_inequality_by_length(s_long: Seq<char>, s_short: Seq<char>)
    requires
        ValidBitString(s_long),
        ValidBitString(s_short),
        s_long.len() > s_short.len(),
        s_long.len() > 0,
        (s_long.len() > 1 ==> s_long.view_at(0 as nat) != '0'),
        s_short.len() > 0,
        (s_short.len() > 1 ==> s_short.view_at(0 as nat) != '0'),

    ensures Str2Int(s_long) > Str2Int(s_short)
{
    reveal_Str2Int_non_zero_leading_digit();

    let len_short = s_short.len();
    let len_long = s_long.len();

    assert(len_long >= len_short + 1);

    if len_short > 0 {
        assert(Str2Int(s_short) + 1 <= 2u64.pow(len_short as u32) as nat);
    }

    assert(Str2Int(s_long) >= 2u64.pow((len_long - 1) as u32) as nat);

    assert(2u64.pow((len_long - 1) as u32) as nat > (2u64.pow(len_short as u32) as nat - 1)) by {
        assert(len_long - 1 >= len_short);
        if len_short == 0 {
             assert (2u64.pow((len_long - 1) as u32)) as nat > 0;
        } else {
            assert((2u64.pow((len_long - 1) as u32)) as nat >= (2u64.pow(len_short as u32)) as nat);
            assert((2u64.pow(len_short as u32)) as nat > (2u64.pow(len_short as u32)) as nat - 1);
        }
    }
}

proof fn Str2Int_inequality_by_first_diff(s1: Seq<char>, s2: Seq<char>, k: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        0 <= k && k < s1.len(),
        forall |j: int| 0 <= j && j < k ==> s1.view_at(j as nat) == s2.view_at(j as nat),
        s1.view_at(k as nat) == '1',
        s2.view_at(k as nat) == '0',
    ensures Str2Int(s1) > Str2Int(s2)
{
    let len = s1.len();

    if len - 1 - k >= 0 {
        assert(2u64.pow((len - 1 - k) as u32) as nat > (2u64.pow((len - k - 1) as u32) - 1) as nat) by {
            if len - k - 1 <= 0 {
                assert(k == len - 1);
                assert(2u64.pow(0) as nat == 1);
                assert((2u64.pow(0) - 1) as nat == 0);
                assert(1 > 0);
            } else {
                assert(2u64.pow((len - 1 - k) as u32) as nat == 2u64.pow((len - k - 1) as u32) as nat);
                assert(2u64.pow((len - k - 1) as u32) as nat > (2u64.pow((len - k - 1) as u32) - 1) as nat);
            }
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
/* code modified by LLM (iteration 4): Fix type errors related to usize/int and sequence indexing, and change for loop to while. */
{
    let s1_normalized = NormalizeBitString(s1);
    let s2_normalized = NormalizeBitString(s2);

    if s1_normalized@.len() > s2_normalized@.len() {
        proof {
            reveal_Str2Int_non_zero_leading_digit();
            Str2Int_inequality_by_length(s1_normalized@, s2_normalized@);
        }
        1
    } else if s1_normalized@.len() < s2_normalized@.len() {
        proof {
            reveal_Str2Int_non_zero_leading_digit();
            Str2Int_inequality_by_length(s2_normalized@, s1_normalized@);
        }
        -1
    } else {
        let mut i: int = 0; // Changed to int
        while i < s1_normalized@.len()
            invariant
                0 <= i,
                i <= s1_normalized@.len(),
                s1_normalized@.len() == s2_normalized@.len(),
                ValidBitString(s1_normalized@),
                ValidBitString(s2_normalized@),
                forall |j: int| 0 <= j && j < i ==> s1_normalized@.view_at(j as nat) == s2_normalized@.view_at(j as nat),
            decreases (s1_normalized@.len()) - i
        {
            if s1_normalized@.view_at(i as nat) != s2_normalized@.view_at(i as nat) { // Use view_at and cast i to nat
                break;
            }
            i = i + 1;
        }

        if i == s1_normalized@.len() {
            0
        } else if s1_normalized@.view_at(i as nat) == '1' { // Use view_at and cast i to nat
            proof {
                Str2Int_inequality_by_first_diff(s1_normalized@, s2_normalized@, i);
            }
            1
        } else {
            proof {
                Str2Int_inequality_by_first_diff(s2_normalized@, s1_normalized@, i);
            }
            -1
        }
    }
}
// </vc-code>

fn main() {}
}


