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
proof fn lemma_all_zeros_value(s: Seq<char>)
    requires
        ValidBitString(s),
        AllZero(s),
    ensures
        Str2Int(s) == 0,
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        assert(AllZero(s_prefix)) by {
            assert forall |i: int| 0 <= i && i < s_prefix.len() as int implies s_prefix.index(i) == '0' by {
                assert(s_prefix.index(i) == s.index(i));
                assert(s.index(i) == '0');
            }
        }
        lemma_all_zeros_value(s_prefix);
        assert(s.index(s.len() as int - 1) == '0');
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
/* code modified by LLM (iteration 3): fixed int literal types */
{
    let mut result = Vec::<char>::new();
    let mut i: int = 0int;
    while i < n
        invariant
            0 <= i <= n,
            result@.len() == i as nat,
            ValidBitString(result@),
            AllZero(result@),
    {
        result.push('0');
        i = i + 1int;
    }
    proof {
        lemma_all_zeros_value(result@);
    }
    result
}
// </vc-code>

fn main() {}
}


