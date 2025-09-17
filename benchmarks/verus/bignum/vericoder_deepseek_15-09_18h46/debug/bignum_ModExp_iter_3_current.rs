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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

spec fn AllZero(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

// <vc-helpers>
/* helper modified by LLM (iteration 3): Convert Str2Int results to int for executable code */
fn helper_str2int_to_int(s: Seq<char>) -> (res: int)
    requires ValidBitString(s)
    ensures res == Str2Int(s) as int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        let prefix_val = helper_str2int_to_int(prefix);
        let last_char = s.index(s.len() as int - 1);
        if last_char == '1' {
            2 * prefix_val + 1
        } else {
            2 * prefix_val
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Use helper function to convert nat to int for executable code */
{
    let base_int = helper_str2int_to_int(sx@) % helper_str2int_to_int(sz@);
    let mut exponent_int = helper_str2int_to_int(sy@);
    let modulus_int = helper_str2int_to_int(sz@);
    let mut result = 1;
    
    while exponent_int > 0
        invariant
            result as nat == Exp_int(base_int as nat, exponent_int as nat) % modulus_int as nat,
            base_int < modulus_int,
            exponent_int >= 0,
        decreases exponent_int
    {
        if exponent_int % 2 == 1 {
            result = (result * base_int) % modulus_int;
        }
        base_int = (base_int * base_int) % modulus_int;
        exponent_int = exponent_int / 2;
    }
    
    proof {
        lemma_mod_exp_property(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
        assert(result as nat == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    
    let mut res_vec = Vec::new();
    let mut current = result;
    
    while current > 0
        invariant
            current >= 0,
        decreases current
    {
        if current % 2 == 0 {
            res_vec.push('0');
        } else {
            res_vec.push('1');
        }
        current = current / 2;
    }
    
    if res_vec.is_empty() {
        res_vec.push('0');
    }
    
    res_vec.reverse();
    res_vec
}
// </vc-code>

fn main() {}
}


