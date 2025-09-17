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
/* helper modified by LLM (iteration 2): fix assert parentheses and induction */
proof fn AllZero_implies_Str2Int_zero(s: Seq<char>)
    ensures
        AllZero(s) ==> Str2Int(s) == 0,
    decreases s.len()
{
    if s.len() == 0 {
        return;
    }
    let k: int = s.len() as int - 1;
    assert(AllZero(s.subrange(0, k)));
    proof {
        AllZero_implies_Str2Int_zero(s.subrange(0, k));
    }
    assert(Str2Int(s) == 2nat * Str2Int(s.subrange(0, k)) + (if s.index(k) == '1' { 1nat } else { 0nat }));
    assert(s.index(k) == '0');
    assert((if s.index(k) == '1' { 1nat } else { 0nat }) == 0nat);
    assert(Str2Int(s) == 2nat * Str2Int(s.subrange(0, k)));
    assert(Str2Int(s.subrange(0, k)) == 0nat);
    assert(Str2Int(s) == 0nat);
}

/* helper modified by LLM (iteration 2): fix assert parentheses for validity proof */
proof fn AllZero_implies_ValidBitString(s: Seq<char>)
    ensures
        AllZero(s) ==> ValidBitString(s),
    decreases s.len()
{
    if s.len() == 0 {
        return;
    }
    let k: int = s.len() as int - 1;
    assert(AllZero(s.subrange(0, k)));
    proof {
        AllZero_implies_ValidBitString(s.subrange(0, k));
    }
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
    /* code modified by LLM (iteration 2): construct vector of '0' with invariant proofs */
    let mut v = Vec::<char>::new();
    let mut i: int = 0;
    while i < n
        invariant
            v@.len() == i as nat,
            AllZero(v@),
        decreases n - i
    {
        let old_seq = v@;
        v.push('0');
        i = i + 1;
        proof {
            assert(AllZero(old_seq));
            assert(forall |j: int| 0 <= j && j < v@.len() as int ==> if j < old_seq.len() as int { old_seq.index(j) == '0' } else { v@.index(j) == '0' });
            assert(forall |j: int| 0 <= j && j < old_seq.len() as int ==> old_seq.index(j) == '0');
            assert(v@.index(old_seq.len() as int) == '0');
            assert(forall |j: int| 0 <= j && j < v@.len() as int ==> v@.index(j) == '0');
        }
    }
    proof {
        AllZero_implies_ValidBitString(v@);
        AllZero_implies_Str2Int_zero(v@);
    }
    v
}

// </vc-code>

fn main() {}
}


