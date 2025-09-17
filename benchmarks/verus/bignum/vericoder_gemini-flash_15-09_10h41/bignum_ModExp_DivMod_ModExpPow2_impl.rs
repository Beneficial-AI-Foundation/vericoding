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
/* helper modified by LLM (iteration 5): Adding a conversion from int to bitstring helper. */
proof fn int_to_bitstring(i: nat) -> (s: Seq<char>)
    ensures Str2Int(s) == i, ValidBitString(s)
    decreases i
{
    if i == 0 {
        return Seq::singleton('0');
    } else {
        let msb = i % 2 == 1;
        let remaining_int = i / 2;
        let s_prime = int_to_bitstring(remaining_int);
        if msb {
            return s_prime.push('1');
        } else {
            return s_prime.push('0');
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed int usage and cast in line 5. */
{
    let x: nat = Str2Int(sx@);
    let y_nat: nat = Str2Int(sy@);
    let z: nat = Str2Int(sz@);

    if sy@.len() == 1 && sy@[0] == '0' {
        
        let mut res_vec: Vec<char> = Vec::new();
        res_vec.push('1');
        return res_vec;
        
    } else {
        let y_len_nat: nat = sy@.len() as nat;
        let y_prime_seq = sy@.subrange(0, y_len_nat as int - 1);

        let mut res_interim_vec = ModExp_DivMod_ModExpPow2(sx, y_prime_seq.to_vec().as_slice(), sz);
        let res_interim_seq = res_interim_vec@;
        let res_interim: nat = Str2Int(res_interim_seq);

        let last_bit = sy@[y_len_nat as int - 1];

        let result_nat: nat;
        if last_bit == '0' {
            result_nat = (res_interim * res_interim) % z;
        } else {
            result_nat = (x * res_interim * res_interim) % z;
        }
        let s = int_to_bitstring(result_nat);
        return s.to_vec();
    }
}
// </vc-code>

fn main() {}
}
