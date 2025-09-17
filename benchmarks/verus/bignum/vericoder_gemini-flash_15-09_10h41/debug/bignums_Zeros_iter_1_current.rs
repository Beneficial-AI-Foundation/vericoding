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
spec fn Power(x: nat, n: nat) -> nat {
    if n == 0 { 1 }
    else { x * Power(x, n - 1) }
}
// </vc-helpers>

// <vc-spec>
exec fn Zeros(n: int) -> (s: Vec<char>)
  requires n >= 0
  ensures s@.len() == n as nat, ValidBitString(s@), Str2Int(s@) == 0, AllZero(s@)
// </vc-spec>
// <vc-code>
{
    let mut s: Vec<char> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i,
            i <= n,
            s@.len() == i as nat,
            forall |j: int| 0 <= j && j < i ==> s@[j] == '0',
            ValidBitString(s@),
            AllZero(s@),
            Str2Int(s@) == 0
        decreases n - i
    {
        s.push('0');
        i = i + 1;
    }
    s
}
// </vc-code>

fn main() {}
}


