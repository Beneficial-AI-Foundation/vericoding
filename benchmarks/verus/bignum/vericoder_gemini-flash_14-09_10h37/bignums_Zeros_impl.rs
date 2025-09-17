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
/* helper modified by LLM (iteration 5): removed the helper as it was not needed */
// </vc-helpers>

// <vc-spec>
exec fn Zeros(n: int) -> (s: Vec<char>)
  requires n >= 0
  ensures s@.len() == n as nat, ValidBitString(s@), Str2Int(s@) == 0, AllZero(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The error indicated `n as int` was problematic in a concrete context. The verifier doesn't like converting concrete `N` to `int`. Instead, `n` should be used directly. Also removed the `+ 0` type coercion. */
{
    let mut i: nat = 0;
    let mut s: Vec<char> = Vec::new();
    while (i as int) < n
        invariant
            0 <= i as int,
            (i as int) <= n,
            s@.len() == i as nat,
            forall |j: int| 0 <= j && j < i as int ==> s@.index(j) == '0'
    {
        s.push('0');
        i = i + 1;
    }
    s
}
// </vc-code>

fn main() {}
}


