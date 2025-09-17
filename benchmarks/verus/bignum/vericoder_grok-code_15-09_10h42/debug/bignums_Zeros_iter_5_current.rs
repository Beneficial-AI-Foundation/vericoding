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
spec fn Str2Int(s: Seq<char>) -> nat
    requires ValidBitString(s)
    decreases s.len()
{
    if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

/* helper modified by LLM (iteration 5): added lemma to prove ValidBitString holds for all-zero string */
proof fn lemma_validbitstring_allzero(s: Seq<char>)
    requires AllZero(s)
    ensures ValidBitString(s)
    decreases s.len()
{
    if s.len() > 0 {
        lemma_validbitstring_allzero(s.subrange(0, s.len() as int - 1));
        assert(s.index(s.len() as int - 1) == '0');
        assert(s.len() as int > 0);
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
    /* code modified by LLM (iteration 5): implemented Zeros fn with loop to build vector of '0's, added ValidBitString to loop invariant, and called lemmas to prove postconditions */
    let mut vec: Vec<char> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            vec@.len() == i as nat,
            ValidBitString(vec@),
            AllZero(vec@),
        decreases (n - i) as nat
    {
        proof {
            if i > 0 {
                assert(ValidBitString(vec@));
            }
        }
        vec.push('0');
        i = i + 1;
    }
    proof {
        lemma_validbitstring_allzero(vec@);
        lemma_str2int_allzero(vec@);
    }
    return vec;
}
// </vc-code>

fn main() {}
}


