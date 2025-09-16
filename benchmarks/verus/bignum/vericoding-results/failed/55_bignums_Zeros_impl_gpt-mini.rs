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
/* helper modified by LLM (iteration 10): AllZero implies Str2Int == 0 */
proof fn AllZero_implies_Str2Int_zero(s: Seq<char>)
    ensures
        AllZero(s) ==> Str2Int(s) == 0nat,
    decreases s.len()
{
    if s.len() == 0 { return; }
    if !AllZero(s) { return; }
    let len_int = s.len() as int;
    let k: int = len_int - 1;
    let prefix = s.subrange(0, k);
    proof { AllZero_implies_Str2Int_zero(prefix); }
    assert(Str2Int(s) == 2nat * Str2Int(prefix) + (if s.index(k) == '1' { 1nat } else { 0nat }));
    assert(s.index(k) == '0');
    assert((if s.index(k) == '1' { 1nat } else { 0nat }) == 0nat);
    assert(Str2Int(prefix) == 0nat);
    assert(Str2Int(s) == 0nat);
}

/* helper modified by LLM (iteration 10): AllZero implies ValidBitString */
proof fn AllZero_implies_ValidBitString(s: Seq<char>)
    ensures
        AllZero(s) ==> ValidBitString(s),
    decreases s.len()
{
    if s.len() == 0 { return; }
    if !AllZero(s) { return; }
    assert(forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0');
    assert(forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1'));
}

// </vc-helpers>

// <vc-spec>
exec fn Zeros(n: int) -> (s: Vec<char>)
  requires n >= 0
  ensures s@.len() == n as nat, ValidBitString(s@), Str2Int(s@) == 0, AllZero(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): construct vector of '0' using usize loop counter */
    let mut v = Vec::<char>::new();
    let m: usize = n as usize;
    let mut i: usize = 0usize;
    while i < m
        invariant
            v@.len() == i as nat,
            AllZero(v@),
        decreases m - i
    {
        v.push('0');
        proof {
            assert(v@.len() == (i + 1) as nat);
            assert(v@.index(i as int) == '0');
            assert(forall |j: int| 0 <= j && j < v@.len() as int ==> v@.index(j) == '0');
        }
        i = i + 1;
    }
    proof {
        assert(AllZero(v@));
        AllZero_implies_ValidBitString(v@);
        AllZero_implies_Str2Int_zero(v@);
        assert(ValidBitString(v@));
        assert(Str2Int(v@) == 0nat);
    }
    v
}

// </vc-code>

fn main() {}
}


