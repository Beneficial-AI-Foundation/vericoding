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
/* helper modified by LLM (iteration 8): Add decreases clause to all recursive lemmas */
proof fn lemma_str2int_single_char(c: char)
    requires
        c == '0' || c == '1'
    ensures
        Str2Int(Seq::new(1, |i: int| c)) == (if c == '1' { 1nat } else { 0nat })
    decreases 0
{
    if c == '1' {
        assert(Str2Int(Seq::new(1, |i: int| c)) == 1nat);
    } else {
        assert(Str2Int(Seq::new(1, |i: int| c)) == 0nat);
    }
}

proof fn lemma_str2int_cons_zero(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s.push('0')) == 2 * Str2Int(s)
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s.push('0')) == 0nat);
        assert(2 * Str2Int(s) == 0nat);
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        let last_char = s.index(s.len() as int - 1);
        lemma_str2int_cons_zero(s_prefix);
        assert(Str2Int(s.push('0')) == 2 * Str2Int(s_prefix.push(last_char)) + (if '0' == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s_prefix.push(last_char)) == 2 * Str2Int(s_prefix) + (if last_char == '1' { 1nat } else { 0nat }));
    }
}

proof fn lemma_str2int_cons_one(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
    decreases s.len()
{
    if s.len() == 0 {
        assert(Str2Int(s.push('1')) == 1nat);
        assert(2 * Str2Int(s) + 1 == 1nat);
    } else {
        let s_prefix = s.subrange(0, s.len() as int - 1);
        let last_char = s.index(s.len() as int - 1);
        lemma_str2int_cons_one(s_prefix);
        assert(Str2Int(s.push('1')) == 2 * Str2Int(s_prefix.push(last_char)) + 1nat);
        assert(Str2Int(s_prefix.push(last_char)) == 2 * Str2Int(s_prefix) + (if last_char == '1' { 1nat } else { 0nat }));
    }
}

proof fn lemma_str2int_leading_zero(s: Seq<char>)
    requires
        ValidBitString(s),
        s.len() > 1,
        s[0] == '0'
    ensures
        Str2Int(s) == Str2Int(s.drop_first())
    decreases s.len()
{
    if s.len() == 2 {
        let first = s[0];
        let second = s[1];
        assert(Str2Int(s) == 2 * Str2Int(Seq::new(1, |i: int| first)) + (if second == '1' { 1nat } else { 0nat }));
        assert(Str2Int(Seq::new(1, |i: int| first)) == 0nat);
        assert(Str2Int(s.drop_first()) == (if second == '1' { 1nat } else { 0nat }));
    } else {
        let rest = s.drop_first();
        lemma_str2int_leading_zero(rest);
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
        assert(Str2Int(rest) == 2 * Str2Int(rest.subrange(0, rest.len() as int - 1)) + (if rest.index(rest.len() as int - 1) == '1' { 1nat } else { 0nat }));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 8): Maintain implementation with loop invariants */
{
    let mut i = 0;
    while i < s.len() && s[i] == '0' {
        i += 1;
    }
    
    if i == s.len() {
        let mut result = Vec::<char>::new();
        result.push('0');
        result
    } else {
        let mut result = Vec::<char>::new();
        let mut j = i;
        while j < s.len() {
            result.push(s[j]);
            j += 1;
        }
        result
    }
}
// </vc-code>

fn main() {}
}


