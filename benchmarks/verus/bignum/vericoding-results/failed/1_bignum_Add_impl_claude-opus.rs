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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
use vstd::arithmetic::power2::*;

proof fn str2int_append_bit(s: Seq<char>, bit: char)
    requires 
        ValidBitString(s),
        bit == '0' || bit == '1',
    ensures 
        ValidBitString(s.push(bit)),
        Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat }),
    decreases s.len(),
{
    assert(s.push(bit).len() == s.len() + 1);
    assert(s.push(bit).subrange(0, s.len() as int) =~= s);
    assert(s.push(bit).index(s.len() as int) == bit);
}

proof fn str2int_zero()
    ensures Str2Int(Seq::<char>::empty()) == 0,
{
}

proof fn valid_bit_string_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures ValidBitString(s.push(c)),
{
    assert forall |i: int| 0 <= i && i < s.push(c).len() as int implies
        s.push(c).index(i) == '0' || s.push(c).index(i) == '1'
    by {
        if i < s.len() as int {
            assert(s.push(c).index(i) == s.index(i));
        } else {
            assert(i == s.len() as int);
            assert(s.push(c).index(i) == c);
        }
    }
}

proof fn valid_bit_string_subrange(s: Seq<char>, start: int, end: int)
    requires
        ValidBitString(s),
        0 <= start <= end <= s.len() as int,
    ensures ValidBitString(s.subrange(start, end)),
{
    assert forall |i: int| 0 <= i && i < s.subrange(start, end).len() as int implies
        s.subrange(start, end).index(i) == '0' || s.subrange(start, end).index(i) == '1'
    by {
        assert(s.subrange(start, end).index(i) == s.index(start + i));
    }
}

proof fn sum_division_lemma(sum: u8)
    requires sum <= 3,
    ensures 
        sum == 2 * (sum >> 1) + (sum & 1),
        (sum >> 1) <= 1,
{
    // Prove by cases with explicit assertions
    if sum == 0 {
        assert(0u8 >> 1 == 0) by (compute);
        assert(0u8 & 1 == 0) by (compute);
    } else if sum == 1 {
        assert(1u8 >> 1 == 0) by (compute);
        assert(1u8 & 1 == 1) by (compute);
    } else if sum == 2 {
        assert(2u8 >> 1 == 1) by (compute);
        assert(2u8 & 1 == 0) by (compute);
    } else {
        assert(sum == 3);
        assert(3u8 >> 1 == 1) by (compute);
        assert(3u8 & 1 == 1) by (compute);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    let mut carry: u8 = 0;
    let mut i: usize = 0;
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 >= len2 { len1 } else { len2 };
    
    proof {
        assert(0 <= 0 && 0 <= len1 as int);
        assert(0 <= 0 && 0 <= len2 as int);
        valid_bit_string_subrange(s1@, 0, 0);
        valid_bit_string_subrange(s2@, 0, 0);
    }
    
    while i < max_len
        invariant
            i <= max_len,
            max_len == if len1 >= len2 { len1 } else { len2 },
            len1 == s1@.len(),
            len2 == s2@.len(),
            carry <= 1,
            ValidBitString(result@),
            ValidBitString(s1@),
            ValidBitString(s2@),
            Str2Int(result@) + (carry as nat) * pow2(i as nat) == 
                Str2Int(s1@.subrange(0, if i <= len1 { i as int } else { len1 as int })) + 
                Str2Int(s2@.subrange(0, if i <= len2 { i as int } else { len2 as int })),
        decreases max_len - i,
    {
        let bit1: u8 = if i < len1 {
            if s1[i] == '1' { 1 } else { 0 }
        } else {
            0
        };
        
        let bit2: u8 = if i < len2 {
            if s2[i] == '1' { 1 } else { 0 }
        } else {
            0
        };
        
        proof {
            assert(bit1 <= 1);
            assert(bit2 <= 1);
            assert(carry <= 1);
        }
        
        let sum = bit1 + bit2 + carry;
        
        proof {
            assert(bit1 <= 1);
            assert(bit2 <= 1);
            assert(carry <= 1);
            assert(sum <= 3);
        }
        
        let new_bit = if (sum & 1) == 1 { '1' } else { '0' };
        let new_carry = sum >> 1;
        
        proof {
            sum_division_lemma(sum);
            assert(sum == 2 * (sum >> 1) + (sum & 1));
            assert(new_carry == sum >> 1);
            assert(new_carry <= 1);
            
            if (sum & 1) == 1 {
                assert(new_bit == '1');
                assert((if new_bit == '1' { 1nat } else { 0nat }) == 1nat);
                assert((sum & 1) as nat == 1nat);
            } else {
                assert((sum & 1) == 0);
                assert(new_bit == '0');
                assert((if new_bit == '1' { 1nat } else { 0nat }) == 0nat);
                assert((sum & 1) as nat == 0nat);
            }
            assert((if new_bit == '1' { 1nat } else { 0nat }) == (sum & 1) as nat);
            
            let curr_end1 = if i <= len1 { i as int } else { len1 as int };
            let curr_end2 = if i <= len2 { i as int } else { len2 as int };
            let next_end1 = if (i + 1) <= len1 { (i + 1) as int } else { len1 as int };
            let next_end2 = if (i + 1) <= len2 { (i + 1) as int } else { len2 as int };
            
            assert(0 <= 0 <= curr_end1 <= len1 as int);
            assert(0 <= 0 <= curr_end2 <= len2 as int);
            assert(0 <= 0 <= next_end1 <= len1 as int);
            assert(0 <= 0 <= next_end2 <= len2 as int);
            
            valid_bit_string_subrange(s1@, 0, curr_end1);
            valid_bit_string_subrange(s2@, 0, curr_end2);
            valid_bit_string_subrange(s1@, 0, next_end1);
            valid_bit_string_subrange(s2@, 0, next_end2);
            
            if i < len1 {
                assert(next_end1 == (i + 1) as int);
                assert(curr_end1 == i as int);
                assert(s1@.subrange(0, next_end1) =~= 
                       s1@.subrange(0, curr_end1).push(s1@.index(i as int)));
                str2int_append_bit(s1@.subrange(0, curr_end1), s1@.index(i as int));
                assert(Str2Int(s1@.subrange(0, next_end1)) == 
                       2 * Str2Int(s1@.subrange(0, curr_end1)) + bit1 as nat);
            } else {
                assert(next_end1 == len1 as int);
                assert(curr_end1 == len1 as int);
                assert(s1@.subrange(0, next_end1) =~= s1@.subrange(0, curr_end1));
                assert(Str2Int(s1@.subrange(0, next_end1)) == Str2Int(s1@.subrange(0, curr_end1)));
                assert(bit1 == 0);
            }
            
            if i < len2 {
                assert(next_end2 == (i + 1) as int);
                assert(curr_end2 == i as int);
                assert(s2@.subrange(0, next_end2) =~= 
                       s2@.subrange(0, curr_end2).push(s2@.index(i as int)));
                str2int_append_bit(s2@.subrange(0, curr_end2), s2@.index(i as int));
                assert(Str2Int(s2@.subrange(0, next_end2)) == 
                       2 * Str2Int(s2@.subrange(0, curr_end2)) + bit2 as nat);
            } else {
                assert(next_end2 == len2 as int);
                assert(curr_end2 == len2 as int);
                assert(s2@.subrange(0, next_end2) =~= s2@.subrange(0, curr_end2));
                assert(Str2Int(s2@.subrange(0, next_end2)) == Str2Int(s2@.subrange(0, curr_end2)));
                assert(bit2 == 0);
            }
            
            valid_bit_string_push(result@, new_bit);
            str2int_append_bit(result@, new_bit);
            
            assert(i < max_len);
            assert(i + 1 > 0);
            lemma_pow2_unfold((i + 1) as nat);
            assert(pow2((i + 1) as nat) == 2 * pow2(i as nat));
            
            assert(sum == bit1 + bit2 + carry);
            assert(new_carry == sum >> 1);
            assert((if new_bit == '1' { 1nat } else { 0nat }) == (sum & 1) as nat);
            assert(sum as nat == 2 * new_carry as nat + (if new_bit == '1' { 1nat } else { 0nat }));
            
            assert(Str2Int(result@.push(new_bit)) == 2 * Str2Int(result@) + (if new_bit == '1' { 1nat } else { 0nat }));
            
            assert(Str2Int(result@) + (carry as nat) * pow2(i as nat) == 
                   Str2Int(s1@.subrange(0, curr_end1)) + Str2Int(s2@.subrange(0, curr_end2)));
            
            assert(2 * Str2Int(result@) + 2 * (carry as nat) * pow2(i as nat) == 
                   2 * Str2Int(s1@.subrange(0, curr_end1)) + 2 * Str2Int(s2@.subrange(0, curr_end2)));
            
            assert(2 * Str2Int(result@) + (sum & 1) as nat + 2 * (new_carry as nat) * pow2(i as nat) ==
                   2 * Str2Int(result@) + (sum & 1) as nat + (new_carry as nat) * pow2((i + 1) as nat));
            
            assert(bit1 as nat + bit2 as nat + carry as nat == sum as nat);
            assert(2 * (new_carry as nat) + (sum & 1) as nat == sum as nat);
            assert(2 * (carry as nat) * pow2(i as nat) + (bit1 as nat + bit2 as nat) * 2 * pow2(i as nat) ==
                   2 * Str2Int(s1@.subrange(0, curr_end1)) + 2 * Str2Int(s2@.subrange(0, curr_end2)));
            
            assert(Str2Int(s1@.subrange(0, next_end1)) + Str2Int(s2@.subrange(0, next_end2)) ==
                   2 * Str2Int(s1@.subrange(0, curr_end1)) + bit1 as nat + 2 * Str2Int(s2@.subrange(0, curr_end2)) + bit2 as nat);
            
            assert(Str2Int(result@.push(new_bit)) + (new_carry as nat) * pow2((i + 1) as nat) ==
                   Str2Int(s1@.subrange(0, next_end1)) + Str2Int(s2@.subrange(0, next_end2)));
        }
        
        result.push(new_bit);
        carry = new_carry;
        i = i + 1;
    }
    
    if carry == 1 {
        proof {
            valid_bit_string_push(result@, '1');
            str2int_append_bit(result@, '1');
            assert(i == max_len);
            assert(s1@.subrange(0, len1 as int) =~= s1@);
            assert(s2@.subrange(0, len2 as int) =~= s2@);
            
            assert(Str2Int(result@.push('1')) == 2 * Str2Int(result@) + 1);
            assert(Str2Int(result@) + pow2(max_len as nat) == Str2Int(s1@) + Str2Int(s2@));
            
            if max_len > 0 {
                lemma_pow2_unfold(max_len as nat);
                lemma_pow2_is_power_of_2(max_len as nat);
            }
            
            assert(Str2Int(result@.push('1')) == Str2Int(s1@) + Str2Int(s2@));
        }
        result.push('1');
    } else {
        proof {
            assert(carry == 0);
            assert(i == max_len);
            assert(s1@.subrange(0, len1 as int) =~= s1@);
            assert(s2@.subrange(0, len2 as int) =~= s2@);
            assert(Str2Int(result@) == Str2Int(s1@) + Str2Int(s2@));
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}