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
proof fn str2int_leading_zero(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 0,
        s[0] == '0',
    ensures
        Str2Int(s) == Str2Int(s.subrange(1, s.len() as int)),
    decreases s.len(),
{
    if s.len() == 1 {
        assert(s.subrange(1, s.len() as int).len() == 0);
        assert(Str2Int(s) == 0);
    } else {
        let s_tail = s.subrange(1, s.len() as int);
        assert(s.subrange(0, s.len() as int - 1)[0] == '0');
        if s.len() == 2 {
            assert(s.subrange(0, 1) =~= seq!['0']);
            assert(Str2Int(s.subrange(0, 1)) == 0);
        } else {
            str2int_leading_zero(s.subrange(0, s.len() as int - 1));
        }
        assert(s_tail.subrange(0, s_tail.len() as int - 1) =~= s.subrange(1, s.len() as int - 1));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed invalid 0nat suffix to just 0 */
    let mut result = Vec::<char>::new();
    let mut found_nonzero = false;
    
    for i in 0..s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@) ==> ValidBitString(result@),
            ValidBitString(s@) ==> (found_nonzero || result@.len() == 0),
            ValidBitString(s@) ==> (!found_nonzero ==> forall |j: int| 0 <= j && j < i ==> s@[j] == '0'),
            ValidBitString(s@) ==> (found_nonzero ==> result@ =~= s@.subrange(i as int - result@.len() as int, i as int)),
            ValidBitString(s@) ==> (found_nonzero && result@.len() > 0 ==> result@[0] != '0'),
    {
        if s[i] == '1' || (s[i] == '0' && found_nonzero) {
            if !found_nonzero {
                found_nonzero = true;
            }
            result.push(s[i]);
        } else if s[i] == '0' && !found_nonzero {
            // Skip leading zeros
        }
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    if ValidBitString(s@) && s@.len() > 0 {
        let mut leading_zeros = 0;
        for j in 0..s.len()
            invariant
                0 <= j <= s.len(),
                0 <= leading_zeros <= j,
                forall |k: int| 0 <= k && k < leading_zeros ==> s@[k] == '0',
                leading_zeros < j ==> s@[leading_zeros as int] != '0',
        {
            if s[j] != '0' {
                break;
            }
            leading_zeros = leading_zeros + 1;
        }
        
        if leading_zeros < s.len() {
            assert(result@ =~= s@.subrange(leading_zeros as int, s@.len() as int));
            let mut k = leading_zeros;
            while k > 0
                invariant
                    0 <= k <= leading_zeros,
                    Str2Int(s@.subrange(k as int, s@.len() as int)) == Str2Int(s@.subrange(leading_zeros as int, s@.len() as int)),
                decreases k,
            {
                proof {
                    str2int_leading_zero(s@.subrange(k as int - 1, s@.len() as int));
                }
                k = k - 1;
            }
            assert(Str2Int(s@) == Str2Int(result@));
        } else {
            assert(forall |i: int| 0 <= i && i < s@.len() ==> s@[i] == '0');
            assert(Str2Int(s@) == 0);
            assert(result@ =~= seq!['0']);
            assert(Str2Int(result@) == 0);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}


