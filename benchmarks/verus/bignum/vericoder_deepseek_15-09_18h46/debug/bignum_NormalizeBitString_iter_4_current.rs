use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fix drop_first usage and lemma implementation */
proof fn lemma_str2int_empty()
    ensures
        Str2Int(Seq::empty()) == 0
{
}

proof fn lemma_str2int_single_char(c: char)
    requires
        c == '0' || c == '1'
    ensures
        Str2Int(Seq::new(1, |i: int| c)) == (if c == '1' { 1nat } else { 0nat })
{
}

proof fn lemma_str2int_cons_zero(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s.push('0')) == 2 * Str2Int(s)
{
}

proof fn lemma_str2int_cons_one(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
}

proof fn lemma_str2int_leading_zero(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 1,
        s[0] == '0'
    ensures
        Str2Int(s) == Str2Int(s.drop_first())
{
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fix drop_first usage and while loop invariants */
{
    let mut t = Vec::<char>::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            t@.len() == i as nat,
            ValidBitString(t@),
            ValidBitString(s@) ==> Str2Int(t@) == Str2Int(s@.subrange(0, i as int)),
            i >= 0
    {
        t.push(s[i]);
        i += 1;
    }
    
    let mut j = 0;
    while j < t.len() && t[j] == '0'
        invariant
            j <= t@.len(),
            ValidBitString(t@),
            ValidBitString(s@) ==> Str2Int(t@) == Str2Int(s@),
            t@.subrange(j as int, t@.len() as int) == t@.drop_first(),
            j >= 0
    {
        j += 1;
    }
    
    if j == t.len() {
        t.truncate(1);
        t[0] = '0';
    } else if j > 0 {
        let mut normalized = Vec::<char>::new();
        let mut k = j;
        
        while k < t.len()
            invariant
                normalized@.len() == (k - j) as nat,
                normalized@ == t@.subrange(j as int, k as int),
                ValidBitString(normalized@),
                k >= j,
                k <= t@.len()
        {
            normalized.push(t[k]);
            k += 1;
        }
        
        t = normalized;
    }
    
    proof {
        lemma_str2int_leading_zero(t@);
    }
    
    t
}
// </vc-code>

fn main() {}
}


