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
/* helper modified by LLM (iteration 4): no code changes, helpers seem correct */
proof fn lemma_all_zero_is_valid_bit_string(s: Seq<char>)
    requires AllZero(s)
    ensures ValidBitString(s)
{
    assert forall |i: int| 0 <= i < s.len() as int implies s[i] == '0' || s[i] == '1' by {
        assert(s[i] == '0');
    }
}

proof fn lemma_AllZero_implies_Str2Int_is_zero(s: Seq<char>)
    requires AllZero(s)
    ensures Str2Int(s) == 0
    decreases s.len()
{
    if s.len() > 0 {
        lemma_AllZero_implies_Str2Int_is_zero(s.subrange(0, s.len() as int - 1));
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
    /* code modified by LLM (iteration 4): fixed mismatched types on integer literals */
    let mut s: Vec<char> = Vec::new();
    let mut i: int = 0int;
    while i < n
        invariant
            0 <= i,
            i <= n,
            s@.len() == i as nat,
            AllZero(s@),
        decreases n - i
    {
        s.push('0');
        i = i + 1int;
    }

    lemma_all_zero_is_valid_bit_string(s@);
    lemma_AllZero_implies_Str2Int_is_zero(s@);

    s
}
// </vc-code>

fn main() {}
}


