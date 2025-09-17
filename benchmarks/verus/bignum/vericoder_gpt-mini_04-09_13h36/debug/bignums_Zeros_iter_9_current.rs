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
proof fn allzero_implies_str2int_zero(s: Seq<char>)
  requires ValidBitString(s) && AllZero(s)
  ensures Str2Int(s) == 0
  decreases s.len()
{
  if s.len() == 0 {
    // base case: Str2Int(empty) == 0 by definition
  } else {
    let last_index = s.len() as int - 1;
    let prefix = s.subrange(0, last_index);
    // last bit is '0'
    assert(s.index(last_index) == '0');
    // prefix inherits ValidBitString and AllZero from s
    assert(forall |i: int| 0 <= i && i < prefix.len() as int ==> (prefix.index(i) == '0' || prefix.index(i) == '1'));
    assert(ValidBitString(prefix));
    assert(forall |i: int| 0 <= i && i < prefix.len() as int ==> prefix.index(i) == '0');
    assert(AllZero(prefix));
    // recurse on prefix
    allzero_implies_str2int_zero(prefix);
    // unfold Str2Int definition for non-empty s
    assert(Str2Int(s) == 2 * Str2Int(prefix) + (if s.index(last_index) == '1' { 1nat } else { 0nat }));
    // last is '0', so contribution is 0
    assert(Str2Int(s) == 2 * Str2Int(prefix));
    // prefix Str2Int == 0 by induction
    assert(Str2Int(prefix) == 0);
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
  let n_nat: nat = n as nat;
  let mut v = Vec::<char>::new();
  let mut i: nat = 0;
  while i < n_nat
    invariant { i <= n_nat }
    invariant { v@.len() == i }
    invariant { ValidBitString(v@) }
    invariant { AllZero(v@) }
    decreases (n_nat - i)
  {
    let old_v = v@;
    v.push('0');
    // length increased
    assert(v@.len() == i + 1);
    // newly pushed element is '0'
    assert(v@.index(i as int) == '0');
    // previous elements are unchanged after push
    assert(forall |j: int| 0 <= j && j < i as int ==> v@.index(j) == old_v.index(j));
    // from AllZero(old_v) we know previous elements were '0'
    assert(forall |j: int| 0 <= j && j < i as int ==> old_v.index(j) == '0');
    // therefore previous elements in new v are '0'
    assert(forall |j: int| 0 <= j && j < i as int ==> v@.index(j) == '0');
    // combine with the new element to get all zeros
    assert(forall |j: int| 0 <= j && j < v@.len() as int ==> v@.index(j) == '0');
    // ValidBitString follows from all elements being '0' (hence either '0' or '1')
    assert(ValidBitString(v@));
    assert(AllZero(v@));
    i += 1;
  }

  proof {
    allzero_implies_str2int_zero(v@);
  }

  return v;
}
// </vc-code>

fn main() {}
}