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
/* helper modified by LLM (iteration 3): added lemma to prove Str2Int(all zeros) == 0 */
proof fn lemma_str2int_allzero(s: Seq<char>)
    requires AllZero(s)
    requires ValidBitString(s)
    ensures Str2Int(s) == 0
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s) == 0);
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        lemma_str2int_allzero(prefix);
        assert(s.index(s.len() as int - 1) == '0');
        assert(Str2Int(s) == 2 * Str2Int(prefix) + 0nat);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Zeros(n: int) -> (s: Vec<char>)
  requires n >= 0
  ensures s@.len() == n as nat, ValidBitString(s@), Str2Int(s@) == 0, AllZero(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): used int for loop variable to avoid non-primitive cast */
{
    let mut vec: Vec<char> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            vec@.len() == i as nat,
            AllZero(vec@)
        decreases (n - i) as nat
    {
        vec.push('0');
        i = i + 1;
    }
    proof {
        lemma_str2int_allzero(vec@);
    }
    return vec;
}
// </vc-code>

fn main() {}
}


