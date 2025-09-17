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
/* helper modified by LLM (iteration 3): fixed Exp_int to Exp */
spec fn Exp(x: nat, y: nat, m: nat) -> nat
  decreases y
{
  if y == 0 { 1 } else { (x * Exp(x, (y - 1) as nat, m)) % m }
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
/* code modified by LLM (iteration 3): fixed type mismatches from int to nat */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);

    let result_num: nat = Exp(x_val, y_val, z_val);

    let mut result_vec = Vec::<char>::new();
    if result_num == 0 && sy@.len() > 0 {
        result_vec.push('0');
    } else {
        let mut temp: nat = result_num;
        while temp > 0 {
            if temp % 2 == 1 {
                result_vec.insert(0, '1');
            } else {
                result_vec.insert(0, '0');
            }
            temp = temp / 2;
        }
    }
    result_vec
}
// </vc-code>

fn main() {}
}


