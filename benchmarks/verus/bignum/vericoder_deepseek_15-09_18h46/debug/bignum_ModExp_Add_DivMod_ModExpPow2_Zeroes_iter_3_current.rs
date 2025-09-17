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
/* helper modified by LLM (iteration 3): Fixed char_to_nat return type and added proper nat operations */
proof fn lemma_str2int_zero(s: Seq<char>)
    requires ValidBitString(s),
    ensures Str2Int(s) >= 0,
{
}

proof fn lemma_subrange_valid(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start <= end <= s.len() as int,
    ensures ValidBitString(s.subrange(start, end)),
{
}

spec fn is_zero_char(c: char) -> bool {
    c == '0'
}

spec fn is_one_char(c: char) -> bool {
    c == '1'
}

exec fn char_to_nat(c: char) -> (res: nat)
    requires is_zero_char(c) || is_one_char(c),
    ensures is_zero_char(c) ==> res == 0nat, is_one_char(c) ==> res == 1nat,
{
    if c == '0' {
        0nat
    } else if c == '1' {
        1nat
    } else {
        unreachable()
    }
}

exec fn double_val(s: Vec<char>) -> (res: Vec<char>)
    requires ValidBitString(s@),
    ensures ValidBitString(res@), Str2Int(res@) == 2 * Str2Int(s@),
{
    proof { lemma_str2int_zero(s@); }
    let mut res_vec = Vec::new();
    res_vec.push('0');
    res_vec.extend_from_slice(&s);
    res_vec
}

proof fn lemma_str2int_sum(s: Seq<char>, val: nat)
    requires ValidBitString(s),
    ensures Str2Int(s.push('0')) + val == 2 * Str2Int(s) + val,
{
}

fn max(a: usize, b: usize) -> usize {
    if a > b { a } else { b }
}

spec fn nat_add_one(n: nat) -> nat {
    n + 1nat
}

spec fn nat_sub_two(n: nat) -> nat {
    n - 2nat
}

spec fn nat_one() -> nat {
    1nat
}

spec fn nat_two() -> nat {
    2nat
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed nat operations, comparisons, and arithmetic */
    if a.is_empty() {
        return Vec::new();
    }
    if b.is_empty() {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    let mut temp = a.to_vec();
    
    for _ in 0..b.len() {
        result = double_val(result);
        if b[0] == '1' {
            let mut carry = false;
            let mut sum_bits = Vec::new();
            
            let max_len = max(result.len(), temp.len());
            for i in 0..max_len {
                let bit1 = if i < result.len() { result[i] } else { '0' };
                let bit2 = if i < temp.len() { temp[i] } else { '0' };
                
                let val1 = char_to_nat(bit1);
                let val2 = char_to_nat(bit2);
                let mut sum = val1 + val2;
                if carry {
                    sum = nat_add_one(sum);
                }
                
                if sum >= nat_two() {
                    carry = true;
                    sum = nat_sub_two(sum);
                } else {
                    carry = false;
                }
                
                sum_bits.push(if sum == nat_one() { '1' } else { '0' });
            }
            
            if carry {
                sum_bits.push('1');
            }
            
            result = sum_bits;
        }
        temp = double_val(temp);
    }
    
    result
}
// </vc-code>

fn main() {}
}

