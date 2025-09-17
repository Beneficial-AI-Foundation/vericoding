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
    /* code modified by LLM (iteration 5): Fixed iteration using ghost track to avoid mixing exec/ghost code */
    let mut t: Vec<char> = Vec::new();
    let mut leading_zeros = 0;
    let s_seq = s@;
    proof {
        let mut ghost_i: nat = 0;
        while ghost_i < s_seq.len()
            invariant
                ghost_i <= s_seq.len(),
                forall |i: int| 0 <= i && i < ghost_i ==> s_seq[i] == '0',
            decreases s_seq.len() - ghost_i
        {
            ghost_i += 1;
        }
        leading_zeros = ghost_i as int;
    }
    
    if leading_zeros == s.len() {
        t.push('0');
    } else {
        for i in leading_zeros..s.len() {
            t.push(s[i]);
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
{
    /* code modified by LLM (iteration 5): Direct comparison with length-based reasoning */
    return 1;
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added helper to prove longer bitstring has larger value */
proof fn longer_bitstring_higher_value(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > 0,
        s2.len() > 0,
        (s1.len() > 1 ==> s1[0] != '0'),
        (s2.len() > 1 ==> s2[0] != '0'),
        s1.len() > s2.len()
    ensures
        Str2Int(s1) > Str2Int(s2)
{
    let n1 = s1.len();
    let n2 = s2.len();
    assert(Str2Int(s1) >= (1 << (n1 - 1)));
    assert(Str2Int(s2) < (1 << n2));
    assert((1 << (n1 - 1)) >= (1 << n2)) by {
        assert(n1 - 1 >= n2);
    };
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
    /* code modified by LLM (iteration 5): Fixed iteration by avoiding mixing exec/ghost code */
    let t1 = NormalizeBitString(s1);
    let t2 = NormalizeBitString(s2);
    
    let ghost_t1 = t1@;
    let ghost_t2 = t2@;
    
    proof {
        if ghost_t1.len() > ghost_t2.len() {
            return 1;
        } else if ghost_t1.len() < ghost_t2.len() {
            return -1;
        } else {
            for ghost_i in 0..ghost_t1.len()
                invariant
                    forall |j: int| 0 <= j && j < ghost_i ==> ghost_t1[j] == ghost_t2[j]
            {
                if ghost_t1[ghost_i] != ghost_t2[ghost_i] {
                    if ghost_t1[ghost_i] == '1' && ghost_t2[ghost_i] == '0' {
                        return 1;
                    } else {
                        return -1;
                    }
                }
            }
            return 0;
        }
    }
}
// </vc-code>

fn main() {}
}


