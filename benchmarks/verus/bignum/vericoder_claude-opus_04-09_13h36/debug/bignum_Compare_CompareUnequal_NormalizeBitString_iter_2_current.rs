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
// Lemma: Str2Int of a single '0' is 0
proof fn lemma_str2int_single_zero()
    ensures Str2Int(seq!['0']) == 0
{
    assert(seq!['0'].len() == 1);
    assert(seq!['0'].subrange(0, 0) =~= Seq::<char>::empty());
    assert(Str2Int(Seq::<char>::empty()) == 0);
    assert(seq!['0'].index(0) == '0');
}

// Lemma: Prepending '0' to a valid bit string doesn't change its value
proof fn lemma_prepend_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(seq!['0'] + s) == Str2Int(s)
    decreases s.len()
{
    if s.len() == 0 {
        lemma_str2int_single_zero();
    } else {
        let s_with_zero = seq!['0'] + s;
        assert(s_with_zero.len() == s.len() + 1);
        assert(s_with_zero.subrange(0, s_with_zero.len() as int - 1) =~= seq!['0'] + s.subrange(0, s.len() as int - 1));
        assert(s_with_zero.index(s_with_zero.len() as int - 1) == s.index(s.len() as int - 1));
        
        lemma_prepend_zero(s.subrange(0, s.len() as int - 1));
    }
}

// Lemma: Multiple leading zeros can be removed one by one
proof fn lemma_remove_leading_zeros(s: Seq<char>, num_zeros: nat)
    requires 
        ValidBitString(s),
        num_zeros > 0,
        num_zeros <= s.len(),
        forall |i: int| 0 <= i && i < num_zeros ==> s.index(i) == '0'
    ensures Str2Int(s) == Str2Int(s.subrange(num_zeros as int, s.len() as int))
    decreases num_zeros
{
    if num_zeros == 1 {
        assert(s.subrange(1, s.len() as int) =~= s.skip(1));
        lemma_prepend_zero(s.skip(1));
        assert(s =~= seq![s.index(0)] + s.skip(1));
        assert(s.index(0) == '0');
    } else {
        let s_without_first = s.skip(1);
        assert(forall |i: int| 0 <= i && i < num_zeros - 1 ==> s_without_first.index(i) == '0');
        lemma_remove_leading_zeros(s_without_first, (num_zeros - 1) as nat);
        lemma_prepend_zero(s_without_first);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    // Check if input is a valid bit string
    let mut is_valid = true;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            is_valid <==> forall |j: int| 0 <= j && j < i ==> (s@[j] == '0' || s@[j] == '1')
    {
        if s[i] != '0' && s[i] != '1' {
            is_valid = false;
        }
        i = i + 1;
    }
    
    if !is_valid || s.len() == 0 {
        // Return "0" for invalid or empty strings
        let mut result = Vec::<char>::new();
        result.push('0');
        proof {
            lemma_str2int_single_zero();
            assert(result@.len() == 1);
            assert(result@[0] == '0');
            assert(ValidBitString(result@));
        }
        return result;
    }
    
    // Find the first non-zero character
    let mut first_nonzero: usize = 0;
    while first_nonzero < s.len() && s[first_nonzero] == '0'
        invariant
            0 <= first_nonzero <= s.len(),
            forall |j: int| 0 <= j && j < first_nonzero ==> s@[j] == '0'
    {
        first_nonzero = first_nonzero + 1;
    }
    
    if first_nonzero == s.len() {
        // All zeros, return "0"
        let mut result = Vec::<char>::new();
        result.push('0');
        proof {
            lemma_str2int_single_zero();
            if s.len() > 0 {
                lemma_remove_leading_zeros(s@, s.len() as nat);
                assert(s@.subrange(s.len() as int, s.len() as int) =~= Seq::<char>::empty());
                assert(Str2Int(s@) == 0);
            }
        }
        return result;
    }
    
    // Copy from first_nonzero to end
    let mut result = Vec::<char>::new();
    let mut j: usize = first_nonzero;
    while j < s.len()
        invariant
            first_nonzero <= j <= s.len(),
            result@.len() == j - first_nonzero,
            forall |k: int| 0 <= k && k < result@.len() ==> result@[k] == s@[first_nonzero as int + k],
            forall |k: int| 0 <= k && k < result@.len() ==> (result@[k] == '0' || result@[k] == '1')
    {
        result.push(s[j]);
        j = j + 1;
    }
    
    proof {
        assert(result@.len() == s.len() - first_nonzero);
        assert(result@.len() > 0);
        assert(ValidBitString(result@));
        if result@.len() > 1 {
            assert(result@[0] == s@[first_nonzero as int]);
            assert(s@[first_nonzero as int] != '0');
            assert(result@[0] != '0');
        }
        
        if ValidBitString(s@) && first_nonzero > 0 {
            assert(result@ =~= s@.subrange(first_nonzero as int, s.len() as int));
            lemma_remove_leading_zeros(s@, first_nonzero as nat);
            assert(Str2Int(s@) == Str2Int(result@));
        } else if ValidBitString(s@) && first_nonzero == 0 {
            assert(result@ =~= s@);
            assert(Str2Int(s@) == Str2Int(result@));
        }
    }
    
    return result;
}
// </vc-code>

fn main() {}
}