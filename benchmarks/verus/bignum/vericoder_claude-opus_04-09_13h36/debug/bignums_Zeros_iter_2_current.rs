use vstd::prelude::*;

verus! {

spec fn AllZero(s: Seq<char>) -> bool
{
  s.len() == 0 || forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
proof fn lemma_str2int_all_zeros(s: Seq<char>)
    requires AllZero(s),
             ValidBitString(s),
    ensures Str2Int(s) == 0,
    decreases s.len(),
{
    if s.len() == 0 {
        // Base case: empty sequence
        assert(Str2Int(s) == 0);
    } else {
        // Inductive case
        let s_prefix = s.subrange(0, s.len() as int - 1);
        
        // Prove that s_prefix is also AllZero
        assert forall |i: int| 0 <= i && i < s_prefix.len() as int implies s_prefix.index(i) == '0' by {
            assert(s_prefix.index(i) == s.index(i));
            assert(s.index(i) == '0');
        }
        assert(AllZero(s_prefix));
        
        // Prove that s_prefix is ValidBitString
        assert forall |i: int| 0 <= i && i < s_prefix.len() as int 
            implies (s_prefix.index(i) == '0' || s_prefix.index(i) == '1') by {
            assert(s_prefix.index(i) == s.index(i));
        }
        assert(ValidBitString(s_prefix));
        
        // Apply induction hypothesis
        lemma_str2int_all_zeros(s_prefix);
        assert(Str2Int(s_prefix) == 0);
        
        // The last character is '0' since AllZero(s)
        assert(s.index(s.len() as int - 1) == '0');
        
        // Calculate Str2Int(s)
        assert(Str2Int(s) == 2 * Str2Int(s_prefix) + 0);
        assert(Str2Int(s) == 0);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Zeros(n: int) -> (s: Vec<char>)
  requires n >= 0
  ensures s@.len() == n as nat, ValidBitString(s@), Str2Int(s@) == 0, AllZero(s@)
// </vc-spec>
// <vc-code>
{
    let mut s = Vec::<char>::new();
    let mut i: usize = 0;
    let n_usize = n as usize;
    
    while i < n_usize
        invariant
            n >= 0,
            n_usize == n as usize,
            i <= n_usize,
            s@.len() == i as nat,
            ValidBitString(s@),
            AllZero(s@),
            Str2Int(s@) == 0,
    {
        let old_s = s;
        s.push('0');
        
        // Prove that the new sequence is AllZero
        assert forall |j: int| 0 <= j && j < s@.len() as int implies s@.index(j) == '0' by {
            if j < old_s@.len() as int {
                assert(s@.index(j) == old_s@.index(j));
                assert(old_s@.index(j) == '0');
            } else {
                assert(j == old_s@.len() as int);
                assert(s@.index(j) == '0');
            }
        }
        assert(AllZero(s@));
        
        // Prove that the new sequence is ValidBitString
        assert forall |j: int| 0 <= j && j < s@.len() as int 
            implies (s@.index(j) == '0' || s@.index(j) == '1') by {
            assert(s@.index(j) == '0');
        }
        assert(ValidBitString(s@));
        
        // Use the lemma to prove Str2Int(s@) == 0
        lemma_str2int_all_zeros(s@);
        
        i = i + 1;
    }
    
    s
}
// </vc-code>

fn main() {}
}