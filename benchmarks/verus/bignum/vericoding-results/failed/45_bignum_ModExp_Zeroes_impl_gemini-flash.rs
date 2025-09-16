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
/* helper modified by LLM (iteration 10): Removed `nat_to_seq_char_recursive` as it's not needed and has issues. */
spec fn div_by_2(n: nat) -> nat {
    (n / 2) as nat
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Removed `nat_to_seq_char_recursive` to fix type error. Used `Str2Int` from `vstd` itself to convert `nat` to `Seq<char>`. */
{
    let x: nat = Str2Int(sx@);
    let y: nat = Str2Int(sy@);
    let z: nat = Str2Int(sz@);

    if y == 0 {
        return vec!['1'];
    }

    let mut current_result_nat: nat = 1;
    let mut xx: nat = x % z;
    let mut yy: nat = y;

    while yy > 0
        invariant
            current_result_nat < z,
            xx < z,
            yy >= 0,
        decreases yy
    {
        if yy % 2 == 1 {
            current_result_nat = (current_result_nat * xx) % z;
        }
        xx = (xx * xx) % z;
        yy = div_by_2(yy);
    }
    
    let res_str = vstd::string::string_to_ascii_chars(current_result_nat.to_string());
    let mut final_vec = Vec::<char>::new();
    let mut i: int = 0;
    while i < res_str.len()
        invariant
            0 <= i,
            i <= res_str.len(),
            final_vec.len() == i,
    {
        final_vec.push(res_str.index(i));
        i = i + 1;
    }
    final_vec
}
// </vc-code>

fn main() {}
}
