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
/* helper modified by LLM (iteration 2): Provided proper suffix for literal `1nat` */
spec fn ModExp(x: nat, y: nat, z: nat) -> nat {
    if y == 0 {
        1nat % z
    } else if y % 2 == 0 {
        let half_y = (y / 2) as nat;
        let res = ModExp(x, half_y, z);
        (res * res) % z
    } else {
        let res = ModExp(x, (y - 1) as nat, z);
        (x * res) % z
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): `nat` type consistency, `Seq::<T>::new` arguments, `to_vec` method for `Seq` */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_int = ModExp(x_int, y_int, z_int);

    // Convert the resulting integer back to a bit string
    fn int_to_bit_string(n: nat) -> Seq<char>
        ensures ValidBitString(int_to_bit_string(n))
    {
        if n == (0 as nat) {
            seq!['0']
        } else {
            let mut s = Seq::<char>::new(0, |i| '0'); // Initialize with a dummy value, length 0
            let mut temp_n: nat = n;
            while temp_n > (0 as nat)
                invariant
                    temp_n >= (0 as nat),
                    ValidBitString(s),
            {
                if temp_n % (2 as nat) == (1 as nat) {
                    s = seq!['1'].add(s);
                } else {
                    s = seq!['0'].add(s);
                }
                temp_n = temp_n / (2 as nat);
            }
            s
        }
    }

    let res_seq = int_to_bit_string(result_int);
    let mut res_vec: Vec<char> = Vec::<char>::new();
    res_vec.extend_from_slice(&res_seq.into_vec()); // Changed to_vec to into_vec
    res_vec
}
// </vc-code>

fn main() {}
}
