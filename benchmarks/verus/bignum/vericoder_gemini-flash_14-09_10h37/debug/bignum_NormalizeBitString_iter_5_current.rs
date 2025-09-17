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
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added proof for lemma_validate_not_empty */
proof fn lemma_validate_not_empty(s: Seq<char>) 
  recommends ValidBitString(s)
  ensures (Str2Int(s) > 0) == (s.len() > 0)
{
  if s.len() == 0 {
    assert(Str2Int(s) == 0);
  } else {
    assert(Str2Int(s) >= 0);
    if s.index(s.len() as int - 1) == '1' {
      assert(Str2Int(s) > 0);
    } else if s.index(s.len() as int - 1) == '0' {
        if s.len() > 1 {
            lemma_validate_not_empty(s.subrange(0, s.len() as int - 1));
            assert((Str2Int(s.subrange(0, s.len() as int - 1)) > 0) == (s.subrange(0, s.len() as int - 1).len() > 0));
            if s.subrange(0, s.len() as int - 1).len() > 0 {
                assert(Str2Int(s) > 0);
            } else {
                assert(Str2Int(s) == 0);
            }
        } else {
            assert(Str2Int(s) == 0);
        }
    }
  }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added assert statements and ensures conditions to match specification */
{
    let mut i: usize = 0;
    while i < s.len()
        invariant 0 <= i && i <= s.len()
        decreases s.len() - i
    {
        if s[i] == '1' {
            break;
        }
        i = i + 1;
    }

    let mut t_vec: Vec<char> = Vec::new();

    if i == s.len() {
        t_vec.push('0');
        // Proof that ValidBitString(['0']) is true
        proof {
            assert(ValidBitString(seq!['0']));
        }
        assert(t_vec@.len() == 1);
        assert(t_vec@[0] == '0');
        assert(Str2Int(s@) == 0);
        assert(Str2Int(t_vec@) == 0);
    } else {
        let mut j: usize = i;
        while j < s.len()
            invariant i <= j && j <= s.len()
            invariant ValidBitString(s@.subrange(i as int, j as int))
            decreases s.len() - j
        {
            t_vec.push(s[j]);
            j = j + 1;
        }
        // Proof that ValidBitString(t_vec@) is true
        proof {
            assert(ValidBitString(s@));
            assert forall |k: int| 0 <= k && k < t_vec@.len() as int implies
                (t_vec@[k] == '0' || t_vec@[k] == '1') by {
                assert(s@[i as int + k] == '0' || s@[i as int + k] == '1');
            }
            assert(ValidBitString(t_vec@));
        }
    }
    
    proof {
      if s@.len() == 0 {
        assert(Str2Int(s@) == 0);
      }
      else {
        lemma_validate_not_empty(s@);
        if Str2Int(s@) > 0 {
          assert(s@.len() > 0);
        }
      }

      if ValidBitString(s@) {
        if i < s.len() {
          assert(s@.subrange(i as int, s@.len() as int) == t_vec@);
          assert(Str2Int(s@.subrange(i as int, s@.len() as int)) == Str2Int(t_vec@));
          assert(Str2Int(s@) == Str2Int(t_vec@));
        } else if s@.len() > 0 {
          // Only encountered leading zeros, original string represents 0
          assert(Str2Int(s@) == 0);
          assert(Str2Int(t_vec@) == 0);
        }

      }

      if t_vec@.len() > 1 {
        assert(t_vec@[0] != '0'); // Because we skipped all leading zeros
      }
      assert(t_vec@.len() > 0); // Either '0' or actual bits
    }
    
    t_vec
}
// </vc-code>

fn main() {}
}


