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
proof fn lemma_all_zero_str2int_is_zero(s: Seq<char>)
    requires ValidBitString(s), AllZero(s)
    ensures Str2Int(s) == 0
    decreases s.len()
{
    if s.len() == 0 {
        // Base case: empty sequence
    } else {
        // Inductive case
        let prefix = s.subrange(0, s.len() as int - 1);
        let last_char = s.index(s.len() as int - 1);
        
        // Show that prefix is also all zeros and valid
        assert forall |i: int| 0 <= i && i < prefix.len() as int implies prefix.index(i) == '0' by {
            assert(prefix.index(i) == s.index(i));
            assert(s.index(i) == '0');
        }
        assert(AllZero(prefix));
        
        assert forall |i: int| 0 <= i && i < prefix.len() as int implies (prefix.index(i) == '0' || prefix.index(i) == '1') by {
            assert(prefix.index(i) == s.index(i));
        }
        assert(ValidBitString(prefix));
        
        // Recursive call
        lemma_all_zero_str2int_is_zero(prefix);
        
        // Since all chars are '0', the last char is '0'
        assert(last_char == '0');
        
        // Therefore Str2Int(s) = 2 * 0 + 0 = 0
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
    let mut result = Vec::<char>::new();
    let mut i = 0;
    
    while i < n
        invariant 
            0 <= i <= n,
            result@.len() == i as nat,
            ValidBitString(result@),
            AllZero(result@),
            Str2Int(result@) == 0
    {
        result.push('0');
        
        // Prove that adding '0' preserves AllZero
        assert(AllZero(result@)) by {
            let new_seq = result@;
            assert forall |j: int| 0 <= j && j < new_seq.len() as int implies new_seq.index(j) == '0' by {
                if j < i {
                    assert(new_seq.index(j) == old(result)@.index(j));
                } else {
                    assert(j == i);
                    assert(new_seq.index(j) == '0');
                }
            }
        }
        
        // Prove that adding '0' preserves ValidBitString
        assert(ValidBitString(result@)) by {
            let new_seq = result@;
            assert forall |j: int| 0 <= j && j < new_seq.len() as int implies (new_seq.index(j) == '0' || new_seq.index(j) == '1') by {
                if j < i {
                    assert(new_seq.index(j) == old(result)@.index(j));
                } else {
                    assert(j == i);
                    assert(new_seq.index(j) == '0');
                }
            }
        }
        
        // Prove Str2Int(result@) == 0
        lemma_all_zero_str2int_is_zero(result@);
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}