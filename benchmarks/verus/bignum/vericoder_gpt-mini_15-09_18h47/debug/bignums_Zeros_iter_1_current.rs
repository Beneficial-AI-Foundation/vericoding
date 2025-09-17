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
proof fn AllZero_implies_Str2Int_zero(s: Seq<char>)
    ensures
        AllZero(s) ==> Str2Int(s) == 0,
    decreases s.len()
{
    if s.len() == 0 {
        return;
    }
    let k: int = s.len() as int - 1;
    assert AllZero(s.subrange(0, k));
    proof {
        AllZero_implies_Str2Int_zero(s.subrange(0, k));
    }
    // unfold definition of Str2Int for s
    assert Str2Int(s) == 2nat * Str2Int(s.subrange(0, k)) + (if s.index(k) == '1' { 1nat } else { 0nat });
    // since AllZero(s), last bit is '0'
    assert s.index(k) == '0';
    assert (if s.index(k) == '1' { 1nat } else { 0nat }) == 0nat;
    assert Str2Int(s) == 2nat * Str2Int(s.subrange(0, k));
    // by induction Str2Int(subrange) == 0
    assert Str2Int(s.subrange(0, k)) == 0nat;
    assert Str2Int(s) == 0nat;
}

proof fn AllZero_implies_ValidBitString(s: Seq<char>)
    ensures
        AllZero(s) ==> ValidBitString(s),
    decreases s.len()
{
    if s.len() == 0 {
        return;
    }
    let k: int = s.len() as int - 1;
    assert AllZero(s.subrange(0, k));
    proof {
        AllZero_implies_ValidBitString(s.subrange(0, k));
    }
    // every character is '0', so it is a valid bit
    assert forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1');
}

// </vc-helpers>

// <vc-spec>
exec fn Zeros(n: int) -> (s: Vec<char>)
  requires n >= 0
  ensures s@.len() == n as nat, ValidBitString(s@), Str2Int(s@) == 0, AllZero(s@)
// </vc-spec>
// <vc-code>
{
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
            // show AllZero holds after appending '0'
            assert forall |j: int| 0 <= j && j < v@.len() as int ==>
                if j < old_seq.len() as int { old_seq.index(j) == '0' } else { v@.index(j) == '0' };
            assert forall |j: int| 0 <= j && j < old_seq.len() as int ==> old_seq.index(j) == '0';
            assert v@.index(old_seq.len() as int) == '0';
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


