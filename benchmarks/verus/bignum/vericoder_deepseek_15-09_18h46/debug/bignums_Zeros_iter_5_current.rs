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
/* helper modified by LLM (iteration 5): Fixed type annotations and simplified helpers */
spec fn seq_zero(n: nat) -> Seq<char> {
    if n == 0 {
        Seq::empty()
    } else {
        seq_zero((n - 1) as nat).push('0')
    }
}

proof fn lemma_str2int_zero(n: nat)
    ensures Str2Int(seq_zero(n)) == 0
{
    if n > 0 {
        lemma_str2int_zero((n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Zeros(n: int) -> (s: Vec<char>)
  requires n >= 0
  ensures s@.len() == n as nat, ValidBitString(s@), Str2Int(s@) == 0, AllZero(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatch errors */
{
    let mut s = Vec::new();
    let mut i: int = 0;
    
    while i < n
        invariant
            0 <= i && i <= n,
            s@.len() == i as nat,
            AllZero(s@),
            ValidBitString(s@),
            Str2Int(s@) == 0
    {
        s.push('0');
        i = i + 1;
    }
    
    s
}
// </vc-code>

fn main() {}
}


