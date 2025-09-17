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
    // Str2Int(empty) == 0 by definition
  } else {
    let last_index = s.len() as int - 1;
    // prefix is all but last char
    let prefix = s.subrange(0, last_index);
    // From AllZero, last bit is '0' and prefix is all zero
    assert(s.index(last_index) == '0');
    // prefix satisfies ValidBitString and AllZero
    // Recurse on prefix
    allzero_implies_str2int_zero(prefix);
    // By definition of Str2Int on non-empty sequences:
    // Str2Int(s) == 2 * Str2Int(prefix) + (if last == '1' {1} else {0})
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
  let mut v = Vec::<char>::new();
  let mut i: int = 0;
  while i < n
    invariant 0 <= i && i <= n;
    invariant v@.len() == i as nat;
    invariant ValidBitString(v@);
    invariant AllZero(v@);
    decreases n - i;
  {
    v.push('0');
    i += 1;
  }

  proof {
    // From AllZero and ValidBitString of v@, conclude Str2Int(v@) == 0
    allzero_implies_str2int_zero(v@);
  }

  return v;
}
// </vc-code>

fn main() {}
}