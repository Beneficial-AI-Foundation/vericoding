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
/* helper modified by LLM (iteration 10): fix nat to u64 conversion and add proper helpers */
fn nat_to_u64(n: nat) -> (res: u64)
    ensures res == n as u64
{
    if n == 0 {
        0
    } else {
        let prev = nat_to_u64((n - 1) as nat);
        prev + 1
    }
}

proof fn lemma_nat_to_u64_valid(n: nat)
    ensures nat_to_u64(n) == n as u64
{
    if n > 0 {
        lemma_nat_to_u64_valid((n - 1) as nat);
    }
}

spec fn power(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * power(base, (exp - 1) as nat)
    }
}

proof fn lemma_power_of_two_nonzero(n: nat)
    ensures power(2, n) > 0
{
    if n > 0 {
        lemma_power_of_two_nonzero((n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): fix nat to u64 conversion error */
{
    let mut result = Vec::<char>::new();
    let a_val = Str2Int(a@);
    let b_val = Str2Int(b@);
    
    let exp = a_val + b_val;
    
    let temp_exec: u64 = nat_to_u64(exp);
    let mut temp = temp_exec;
    
    while temp > 0
        invariant
            ValidBitString(result@),
    {
        if temp % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        temp = temp / 2;
    }
    
    result.reverse();
    if result.is_empty() {
        result.push('0');
    }
    result
}
// </vc-code>

fn main() {}
}

