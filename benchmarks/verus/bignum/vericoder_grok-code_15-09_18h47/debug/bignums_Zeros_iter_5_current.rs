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
/* code modified by LLM (iteration 5): Fixed type mismatch by using usize for loop index and casting n to usize */
    let mut v = Vec::new();
    let mut i: usize = 0;
    let n_usize = n as usize;
    while i < n_usize
        invariant
            0 <= i as nat <= n as nat,
            v@.len() == i as nat,
            forall |j: nat| 0 <= j < i ==> v@[j] == '0',
        decreases n_usize - i
    {
        v.push('0');
        i = i + 1;
    }
    return v;
}
// </vc-code>

fn main() {}
}


