
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
/* helper modified by LLM (iteration 8): fix nat comparison issues */
spec fn bits_to_nat(bits: Seq<char>) -> nat
{
    Str2Int(bits)
}

spec fn nat_to_bits_helper(n: nat, acc: Seq<char>) -> Seq<char>
    decreases n
{
    if n == 0nat {
        if acc.len() == 0 { seq!['0'] } else { acc }
    } else {
        let bit = if n % 2nat == 1nat { '1' } else { '0' };
        nat_to_bits_helper(n / 2nat, seq![bit] + acc)
    }
}

spec fn nat_to_bits(n: nat) -> Seq<char>
{
    nat_to_bits_helper(n, seq![])
}

exec fn nat_to_bits_exec(n: nat) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        res@ == nat_to_bits(n)
{
    if n == 0nat {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut num = n;
        while num > 0nat
            invariant
                ValidBitString(result@)
        {
            let bit = if num % 2nat == 1nat { '1' } else { '0' };
            result.insert(0, bit);
            num = num / 2nat;
        }
        result
    }
}

proof fn nat_to_bits_valid(n: nat)
    ensures ValidBitString(nat_to_bits(n))
{
}

proof fn bits_nat_roundtrip(bits: Seq<char>)
    requires ValidBitString(bits)
    ensures nat_to_bits(bits_to_nat(bits)) == bits || (bits.len() > 1 && bits[0] == '0')
{
}

proof fn nat_bits_roundtrip(n: nat)
    ensures bits_to_nat(nat_to_bits(n)) == n
{
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 8): use proper nat literals */
    let dividend_nat = Str2Int(dividend@);
    let divisor_nat = Str2Int(divisor@);
    
    let quotient_nat = dividend_nat / divisor_nat;
    let remainder_nat = dividend_nat % divisor_nat;
    
    let quotient_vec = nat_to_bits_exec(quotient_nat);
    let remainder_vec = nat_to_bits_exec(remainder_nat);
    
    proof {
        nat_to_bits_valid(quotient_nat);
        nat_to_bits_valid(remainder_nat);
        nat_bits_roundtrip(quotient_nat);
        nat_bits_roundtrip(remainder_nat);
    }
    
    (quotient_vec, remainder_vec)
}
// </vc-code>

fn main() {}
}


