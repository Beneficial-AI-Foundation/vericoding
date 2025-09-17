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
/* helper modified by LLM (iteration 4): Fixed nat comparison and type conversion helpers */
proof fn lemma_divmod_property(a: nat, b: nat)
    requires b > 0
    ensures a == b * (a / b) + (a % b), 0 <= a % b < b
{
}

proof fn lemma_str2int_monotonic(a: Seq<char>, b: Seq<char>)
    requires ValidBitString(a), ValidBitString(b), a.len() <= b.len()
    ensures Str2Int(a) <= Str2Int(b)
{
}

proof fn lemma_shift_left_property(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
}

spec fn valid_bitstring_len_gt_zero(s: Seq<char>) -> bool {
    s.len() > 0 && (Str2Int(s) > 0)
}

spec fn nat_eq_zero(n: nat) -> bool { n == 0nat }

spec fn nat_eq_one(n: nat) -> bool { n == 1nat }
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed nat comparisons using spec functions */
{
    let mut quotient: Vec<char> = Vec::new();
    let mut remainder: Vec<char> = Vec::new();
    
    let mut temp: Vec<char> = Vec::new();
    let div_value = Str2Int(divisor@);
    
    let mut i: usize = 0;
    while i < dividend.len()
        invariant
            ValidBitString(temp@),
            ValidBitString(remainder@),
            ValidBitString(quotient@),
            Str2Int(remainder@) < div_value,
            Str2Int(dividend@) == Str2Int(quotient@ + temp@) * div_value + Str2Int(remainder@),
        decreases dividend.len() - i
    {
        temp.push(dividend[i]);
        
        if Str2Int(temp@) >= div_value {
            quotient.push('1');
            let current = Str2Int(temp@);
            proof { lemma_divmod_property(current, div_value); }
            let rem: nat = current % div_value;
            temp.clear();
            
            if !nat_eq_zero(rem) {
                let rem_chars = if nat_eq_one(rem) { vec!['1'] } else { vec!['0'] };
                temp.extend_from_slice(&rem_chars);
            }
        } else {
            quotient.push('0');
        }
        
        i += 1;
    }
    
    remainder = temp;
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}

