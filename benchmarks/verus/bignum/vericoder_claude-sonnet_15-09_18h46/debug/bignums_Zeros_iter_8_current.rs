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
/* helper modified by LLM (iteration 8): fixed lemma syntax by adding proof keyword */
proof fn Zeros_establishes_AllZero(s: Seq<char>)
    requires
        s.len() >= 0,
        forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0',
    ensures
        AllZero(s),
{
}

proof fn Zeros_establishes_ValidBitString(s: Seq<char>)
    requires
        s.len() >= 0,
        forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0',
    ensures
        ValidBitString(s),
{
}

proof fn Zeros_establishes_Str2Int(s: Seq<char>)
    requires
        s.len() >= 0,
        forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0',
        ValidBitString(s),
    ensures
        Str2Int(s) == 0,
    decreases s.len()
{
    if s.len() == 0 {
        
    } else {
        let sub = s.subrange(0, s.len() as int - 1);
        assert(forall |i: int| 0 <= i && i < sub.len() as int ==> sub.index(i) == '0');
        assert(ValidBitString(sub));
        Zeros_establishes_Str2Int(sub);
        assert(s.index(s.len() as int - 1) == '0');
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
    /* code modified by LLM (iteration 8): fixed type error by using usize for loop counter */
    let mut result = Vec::<char>::new();
    let mut i: usize = 0;
    while i < n as usize
        invariant
            0 <= i <= n,
            result@.len() == i,
            forall |j: int| 0 <= j && j < result@.len() as int ==> result@.index(j) == '0',
    {
        result.push('0');
        i = i + 1;
    }
    
    proof {
        let s = result@;
        Zeros_establishes_AllZero(s);
        Zeros_establishes_ValidBitString(s);
        Zeros_establishes_Str2Int(s);
    }
    
    result
}
// </vc-code>

fn main() {}
}


