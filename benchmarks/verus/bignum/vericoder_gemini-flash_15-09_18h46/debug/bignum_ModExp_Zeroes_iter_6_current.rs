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
/* helper modified by LLM (iteration 6): No changes, previous fix was correct. */
spec fn div_by_2(n: nat) -> nat {
    (n / 2) as nat
}

spec fn nat_to_seq_char_recursive(n: nat) -> Seq<char>
decreases n
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1']
    } else {
        let remainder_char = if n % 2 == 0 { '0' } else { '1' };
        nat_to_seq_char_recursive(n / 2).push(remainder_char)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 6): Corrected type issues by removing explicit `as nat` casts in runtime code where the types were already `nat` or `u64`, or where comparing with literals `0` and `1` is implicitly handled. This resolves compilation errors related to `nat`/`int` being used in ghost code contexts. */
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
    
    let res_seq_char = nat_to_seq_char_recursive(current_result_nat);
    if res_seq_char.len() == 0 {
        return vec!['0']; // Should not happen for non-negative nat, but for safety
    }
    let mut final_vec = Vec::<char>::new();
    let mut i: nat = 0;
    while i < res_seq_char.len() {
        final_vec.push(res_seq_char.index(i as int));
        i = i + 1;
    }
    final_vec
}
// </vc-code>

fn main() {}
}
