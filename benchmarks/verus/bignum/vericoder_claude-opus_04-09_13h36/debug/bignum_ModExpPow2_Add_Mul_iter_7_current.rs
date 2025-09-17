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
    assert(s_new.subrange(0, (s_new.len() - 1) as int) =~= s);
    assert(s_new[(s_new.len() - 1) as int] == '0');
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
    let s_new = s.push('1');
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, (s_new.len() - 1) as int) =~= s);
    assert(s_new[(s_new.len() - 1) as int] == '1');
}

proof fn lemma_valid_bit_string_push(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c))
{
    assert forall |i: int| 0 <= i && i < s.push(c).len() as int implies s.push(c)[i] == '0' || s.push(c)[i] == '1' by {
        if i < s.len() as int {
            assert(s.push(c)[i] == s[i]);
        } else {
            assert(i == s.len() as int);
            assert(s.push(c)[i] == c);
        }
    }
}

proof fn lemma_valid_bit_string_subrange(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start <= end <= s.len() as int
    ensures ValidBitString(s.subrange(start, end))
{
    let sub = s.subrange(start, end);
    assert forall |i: int| 0 <= i && i < sub.len() as int implies sub[i] == '0' || sub[i] == '1' by {
        assert(sub[i] == s[start + i]);
    }
}

proof fn lemma_str2int_subrange_extend(s: Seq<char>, i: int)
    requires ValidBitString(s), 0 <= i < s.len() as int
    ensures 
        ValidBitString(s.subrange(0, i)),
        ValidBitString(s.subrange(0, i + 1)),
        Str2Int(s.subrange(0, i + 1)) == 2 * Str2Int(s.subrange(0, i)) + (if s[i] == '1' { 1nat } else { 0nat })
{
    lemma_valid_bit_string_subrange(s, 0, i);
    lemma_valid_bit_string_subrange(s, 0, i + 1);
    let sub_i = s.subrange(0, i);
    let sub_i1 = s.subrange(0, i + 1);
    assert(sub_i1.subrange(0, (sub_i1.len() - 1) as int) =~= sub_i);
    assert(sub_i1[(sub_i1.len() - 1) as int] == s[i]);
}

proof fn lemma_str2int_full(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.subrange(0, s.len() as int)) == Str2Int(s)
{
    assert(s.subrange(0, s.len() as int) =~= s);
}

proof fn lemma_bit_and_mod(x: u8)
    requires x <= 3
    ensures (x & 1) == x % 2
{
    assert(x == 0 || x == 1 || x == 2 || x == 3);
    if x == 0 {
        assert(0u8 % 2u8 == 0u8);
        // Verus knows 0 & 1 == 0 by SMT solver
    } else if x == 1 {
        assert(1u8 % 2u8 == 1u8);
        // Verus knows 1 & 1 == 1 by SMT solver
    } else if x == 2 {
        assert(2u8 % 2u8 == 0u8);
        // Verus knows 2 & 1 == 0 by SMT solver
    } else {
        assert(3u8 % 2u8 == 1u8);
        // Verus knows 3 & 1 == 1 by SMT solver
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
            i <= max_len + 1,
            carry <= 1,
            ValidBitString(result@),
            result.len() == i,
            ValidBitString(s1@),
            ValidBitString(s2@),
            n1 == s1.len(),
            n2 == s2.len(),
            Str2Int(result@) + carry * Exp_int(2, i as nat) == 
                Str2Int(s1@.subrange(0, if i <= n1 { i as int } else { n1 as int })) + 
                Str2Int(s2@.subrange(0, if i <= n2 { i as int } else { n2 as int })),
            i < usize::MAX,
        decreases (max_len + 2) - i,
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
        
        proof {
            assert(bit1 <= 1);
            assert(bit2 <= 1);
            assert(carry <= 1);
            assert(sum <= 3);
            lemma_bit_and_mod(sum);
        }
        
        let new_bit = if (sum & 1) == 1 { '1' } else { '0' };
        let new_carry = sum / 2;
        
        proof {
            let old_result_str2int = Str2Int(result@);
            let old_s1_str2int = Str2Int(s1@.subrange(0, if i <= n1 { i as int } else { n1 as int }));
            let old_s2_str2int = Str2Int(s2@.subrange(0, if i <= n2 { i as int } else { n2 as int }));
            
            if i < n1 {
                lemma_str2int_subrange_extend(s1@, i as int);
            } else {
                lemma_valid_bit_string_subrange(s1@, 0, n1 as int);
            }
            
            if i < n2 {
                lemma_str2int_subrange_extend(s2@, i as int);
            } else {
                lemma_valid_bit_string_subrange(s2@, 0, n2 as int);
            }
            
            let new_s1_str2int = Str2Int(s1@.subrange(0, if (i + 1) <= n1 { (i + 1) as int } else { n1 as int }));
            let new_s2_str2int = Str2Int(s2@.subrange(0, if (i + 1) <= n2 { (i + 1) as int } else { n2 as int }));
            
            if i < n1 {
                assert(new_s1_str2int == 2 * old_s1_str2int + bit1);
            } else {
                assert(new_s1_str2int == old_s1_str2int);
                assert(bit1 == 0);
            }
            
            if i < n2 {
                assert(new_s2_str2int == 2 * old_s2_str2int + bit2);
            } else {
                assert(new_s2_str2int == old_s2_str2int);
                assert(bit2 == 0);
            }
            
            assert(sum == bit1 + bit2 + carry);
            assert((sum & 1) == sum % 2);
            assert(new_carry == sum / 2);
            assert(sum == 2 * new_carry + (sum % 2));
            
            if new_bit == '0' {
                assert((sum & 1) == 0);
                assert(sum % 2 == 0);
                lemma_str2int_append_zero(result@);
                assert(Str2Int(result@.push('0')) == 2 * old_result_str2int);
            } else {
                assert((sum & 1) == 1);
                assert(sum % 2 == 1);
                lemma_str2int_append_one(result@);
                assert(Str2Int(result@.push('1')) == 2 * old_result_str2int + 1);
            }
            
            lemma_valid_bit_string_push(result@, new_bit);
            
            assert(old_result_str2int + carry * Exp_int(2, i as nat) == old_s1_str2int + old_s2_str2int);
            
            let new_result_str2int = if new_bit == '0' { 2 * old_result_str2int } else { 2 * old_result_str2int + 1 };
            assert(new_result_str2int == Str2Int(result@.push(new_bit)));
            
            assert(Exp_int(2, (i + 1) as nat) == 2 * Exp_int(2, i as nat));
            
            // Key assertion: break down the equation step by step
            if i < n1 && i < n2 {
                assert(new_result_str2int == 2 * old_result_str2int + (sum % 2));
                assert(new_s1_str2int == 2 * old_s1_str2int + bit1);
                assert(new_s2_str2int == 2 * old_s2_str2int + bit2);
                assert(2 * old_result_str2int + 2 * carry * Exp_int(2, i as nat) == 
                       2 * old_s1_str2int + 2 * old_s2_str2int);
                assert(new_result_str2int + new_carry * 2 * Exp_int(2, i as nat) == 
                       2 * old_result_str2int + (sum % 2) + 2 * new_carry * Exp_int(2, i as nat));
                assert(sum == bit1 + bit2 + carry);
                assert(new_result_str2int + new_carry * Exp_int(2, (i + 1) as nat) == new_s1_str2int + new_s2_str2int);
            } else if i >= n1 && i < n2 {
                assert(bit1 == 0);
                assert(bit2 == if s2[i] == '1' { 1 } else { 0 });
                assert(new_s1_str2int == old_s1_str2int);
                assert(new_result_str2int + new_carry * Exp_int(2, (i + 1) as nat) == new_s1_str2int + new_s2_str2int);
            } else if i < n1 && i >= n2 {
                assert(bit2 == 0);
                assert(bit1 == if s1[i] == '1' { 1 } else { 0 });
                assert(new_s2_str2int == old_s2_str2int);
                assert(new_result_str2int + new_carry * Exp_int(2, (i + 1) as nat) == new_s1_str2int + new_s2_str2int);
            } else {
                assert(bit1 == 0);
                assert(bit2 == 0);
                assert(new_s1_str2int == old_s1_str2int);
                assert(new_s2_str2int == old_s2_str2int);
                assert(new_result_str2int + new_carry * Exp_int(2, (i + 1) as nat) == new_s1_str2int + new_s2_str2int);
            }
        }
        
        result.push(new_bit);
        carry = new_carry;
        i = i + 1;
    }
    
    proof {
        assert(carry == 0);
        assert(i >= max_len);
        assert(i >= n1);
        assert(i >= n2);
        lemma_str2int_full(s1@);
        lemma_str2int_full(s2@);
        assert(s1@.subrange(0, n1 as int) =~= s1@);
        assert(s2@.subrange(0, n2 as int) =~= s2@);
        assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
    }
    
    result
}
// </vc-code>

fn main() {}
}