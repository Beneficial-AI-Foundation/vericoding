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
/* helper modified by LLM (iteration 7): No changes needed */
spec fn NoHelpers() -> bool { true }
// </vc-helpers>

// <vc-spec>
exec fn Zeros(n: int) -> (s: Vec<char>)
  requires n >= 0
  ensures s@.len() == n as nat, ValidBitString(s@), Str2Int(s@) == 0, AllZero(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): Changed loop variable i to usize to fix compilation type mismatches */
{
    let mut v: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < (n as usize)
        invariant
            0 <= i <= n as usize,
            v@.len() == i,
            forall |j: int| 0 <= j < i as int ==> v@[j] == '0',
        decreases n as usize - i
    {
        v.push('0');
        i = i + 1;
    }
    return v;
}
// </vc-code>

fn main() {}
}


