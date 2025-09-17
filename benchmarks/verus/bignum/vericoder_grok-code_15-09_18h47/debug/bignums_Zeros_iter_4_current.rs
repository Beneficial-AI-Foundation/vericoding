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

// </vc-helpers>

// <vc-spec>
exec fn Zeros(n: int) -> (s: Vec<char>)
  requires n >= 0
  ensures s@.len() == n as nat, ValidBitString(s@), Str2Int(s@) == 0, AllZero(s@)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): Fixed compilation error by using int for loop index instead of usize and removed casting to usize */
    let mut v = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            v@.len() == i as nat,
            forall |j: int| 0 <= j < i ==> v@[j] == '0',
        decreases n - i
    {
        v.push('0');
        i = i + 1;
    }
    return v;
}
// </vc-code>

fn main() {}
}


