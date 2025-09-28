// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Added assertions for bit validity and fixed subrange proofs */
spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1nat } else { 2nat * pow2((n - 1) as nat) }
}

spec fn spec_min(a: int, b: int) -> int {
    if a < b { a } else { b }
}

proof fn str2int_append(s: Seq<char>, c: char)
    requires
        valid_bit_string(s),
        c == '0' || c == '1'
    ensures
        str2int(s.push(c)) == 2nat * str2int(s) + if c == '1' { 1nat } else { 0nat }
{
    let s_new = s.push(c);
    assert(s_new.len() == s_new.len());
    assert(s_new.subrange(0, s_new.len() - 1) =~= s);
    assert(s_new[s_new.len() - 1] == c);
}

proof fn str2int_empty()
    ensures str2int(Seq::<char>::empty()) == 0nat
{
}

proof fn valid_bit_string_subrange(s: Seq<char>, start: int, end: int)
    requires
        valid_bit_string(s),
        0 <= start <= end <= s.len()
    ensures
        valid_bit_string(s.subrange(start, end))
{
    assert forall|i: int| 0 <= i < s.subrange(start, end).len() implies
        s.subrange(start, end)[i] == s[start + i] && (s[start + i] == '0' || s[start + i] == '1');
}

fn add_with_carry(bit1: char, bit2: char, carry: bool) -> (res: (char, bool))
    requires
        bit1 == '0' || bit1 == '1',
        bit2 == '0' || bit2 == '1'
    ensures
        res.0 == '0' || res.0 == '1',
        ({
            let val1: int = if bit1 == '1' { 1int } else { 0int };
            let val2: int = if bit2 == '1' { 1int } else { 0int };
            let carry_val: int = if carry { 1int } else { 0int };
            let sum = val1 + val2 + carry_val;
            let res_bit = if res.0 == '1' { 1int } else { 0int };
            let res_carry = if res.1 { 1int } else { 0int };
            sum == res_bit + 2 * res_carry
        })
{
    let val1 = if bit1 == '1' { 1u8 } else { 0u8 };
    let val2 = if bit2 == '1' { 1u8 } else { 0u8 };
    let carry_val = if carry { 1u8 } else { 0u8 };
    let sum = val1 + val2 + carry_val;
    
    if sum == 0 {
        ('0', false)
    } else if sum == 1 {
        ('1', false)
    } else if sum == 2 {
        ('0', true)
    } else {
        ('1', true)
    }
}
// </vc-helpers>

// <vc-spec>
fn add(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed bit validity assertions and subrange proofs */
    let mut result = Vec::<char>::new();
    let mut carry = false;
    let mut i: usize = 0;
    
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry
        invariant
            i <= max_len,
            valid_bit_string(result@),
            str2int(result@) == (str2int(s1@.subrange(0int, spec_min(i as int, s1.len() as int))) + str2int(s2@.subrange(0int, spec_min(i as int, s2.len() as int))) + if carry { 1nat } else { 0nat }) % pow2(i as nat),
            (str2int(s1@.subrange(0int, spec_min(i as int, s1.len() as int))) + str2int(s2@.subrange(0int, spec_min(i as int, s2.len() as int))) + if carry { 1nat } else { 0nat }) / pow2(i as nat) <= 1nat
        decreases (max_len - i) as int + if carry { 1int } else { 0int }
    {
        let bit1 = if i < s1.len() { s1[i] } else { '0' };
        let bit2 = if i < s2.len() { s2[i] } else { '0' };
        
        // Assert bit validity
        assert(bit1 == '0' || bit1 == '1');
        assert(bit2 == '0' || bit2 == '1');
        
        let (res_bit, new_carry) = add_with_carry(bit1, bit2, carry);
        result.push(res_bit);
        
        proof {
            str2int_append(result@.subrange(0int, (result.len() - 1) as int), res_bit);
            if i < s1.len() {
                assert(s1@.subrange(0int, (i + 1) as int) =~= s1@.subrange(0int, i as int).push(s1@[i as int]));
                valid_bit_string_subrange(s1@, 0int, i as int);
                str2int_append(s1@.subrange(0int, i as int), s1@[i as int]);
            }
            if i < s2.len() {
                assert(s2@.subrange(0int, (i + 1) as int) =~= s2@.subrange(0int, i as int).push(s2@[i as int]));
                valid_bit_string_subrange(s2@, 0int, i as int);
                str2int_append(s2@.subrange(0int, i as int), s2@[i as int]);
            }
        }
        
        carry = new_carry;
        i = i + 1;
    }
    
    proof {
        assert(s1@.subrange(0int, s1.len() as int) =~= s1@);
        assert(s2@.subrange(0int, s2.len() as int) =~= s2@);
        assert(!carry);
    }
    
    result
}
// </vc-code>


}

fn main() {}