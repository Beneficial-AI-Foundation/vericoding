use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
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
proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
    let s_new = s.push('0');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() - 1) =~= s);
    assert(s_new[s_new.len() - 1] == '0');
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
    let s_new = s.push('1');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() - 1) =~= s);
    assert(s_new[s_new.len() - 1] == '1');
}

proof fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c))
{
    assert forall |i: int| 0 <= i && i < s.push(c).len() implies s.push(c)[i] == '0' || s.push(c)[i] == '1' by {
        if i < s.len() {
            assert(s.push(c)[i] == s[i]);
        } else {
            assert(i == s.len());
            assert(s.push(c)[i] == c);
        }
    }
}

proof fn lemma_valid_bit_string_subrange(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start <= end <= s.len()
    ensures ValidBitString(s.subrange(start, end))
{
    let sub = s.subrange(start, end);
    assert forall |i: int| 0 <= i && i < sub.len() implies sub[i] == '0' || sub[i] == '1' by {
        assert(sub[i] == s[start + i]);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    
    let n1 = s1.len();
    let n2 = s2.len();
    let max_len = if n1 >= n2 { n1 } else { n2 };
    
    while i < max_len || carry > 0
        invariant
            i <= max_len || (i == max_len + 1 && carry == 0),
            carry <= 1,
            ValidBitString(result@),
            result.len() == i,
            Str2Int(result@) + carry * Exp_int(2, i as nat) == 
                Str2Int(s1@.subrange(0, if i <= n1 { i as int } else { n1 as int })) + 
                Str2Int(s2@.subrange(0, if i <= n2 { i as int } else { n2 as int })),
    {
        let bit1: u8 = if i < n1 {
            if s1[i] == '1' { 1 } else { 0 }
        } else {
            0
        };
        
        let bit2: u8 = if i < n2 {
            if s2[i] == '1' { 1 } else { 0 }
        } else {
            0
        };
        
        let sum = bit1 + bit2 + carry;
        let new_bit = if (sum & 1) == 1 { '1' } else { '0' };
        carry = sum / 2;
        
        proof {
            lemma_valid_bit_string_subrange(s1@, 0, if i < n1 { (i + 1) as int } else { n1 as int });
            lemma_valid_bit_string_subrange(s2@, 0, if i < n2 { (i + 1) as int } else { n2 as int });
            
            if new_bit == '0' {
                lemma_str2int_append_zero(result@);
            } else {
                lemma_str2int_append_one(result@);
            }
            lemma_valid_bit_string_push(result@, new_bit);
        }
        
        result.push(new_bit);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}