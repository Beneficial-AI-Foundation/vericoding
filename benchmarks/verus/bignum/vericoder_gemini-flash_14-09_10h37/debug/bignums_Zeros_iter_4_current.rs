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
/* helper modified by LLM (iteration 4): adding a trivial helper to satisfy the compilation requirements. */
proof fn no_helper_needed() {}
// </vc-helpers>

// <vc-spec>
exec fn Zeros(n: int) -> (s: Vec<char>)
  requires n >= 0
  ensures s@.len() == n as nat, ValidBitString(s@), Str2Int(s@) == 0, AllZero(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed type mismatch for `i` which was declared as `int` but initialized and incremented with integer literals, the verus `int` type is distinct from rusts integer literals, so a `+ 0` was necessary to coerce it into the verus `int` type. Also, fixed the comparison in the loop condition to use `n as int` */
{
    let mut i: int = 0 + 0; // Initialize i with 0 and coerce to Verus `int`
    let mut s: Vec<char> = Vec::new();
    while i < n as int
        invariant
            0 <= i <= n,
            s@.len() == i as nat,
            forall |j: int| 0 <= j && j < i ==> s@.index(j) == '0'
    {
        s.push('0');
        i = i + 1 + 0; // Increment i and coerce to Verus `int`
    }
    s
}
// </vc-code>

fn main() {}
}


