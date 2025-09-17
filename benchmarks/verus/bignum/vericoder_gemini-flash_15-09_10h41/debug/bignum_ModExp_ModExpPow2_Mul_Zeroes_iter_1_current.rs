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
spec fn ModExpAux(x: nat, y: nat, z: nat) -> nat
decreases y
{
    if y == 0 {
        1 % z
    } else if y % 2 == 0 {
        let res = ModExpAux(x, y / 2, z);
        (res * res) % z
    } else {
        let res = ModExpAux(x, (y - 1) / 2, z);
        (x * res * res) % z
    }
}

spec fn ModExp(x: nat, y: nat, z: nat) -> nat
{
    if z == 0 { 0 } else { ModExpAux(x % z, y, z) }
}

spec fn NatToBitString(n: nat) -> Seq<char>
decreases n
{
    if n == 0 { Seq::singleton('0') }
    else {
        let rem = n % 2;
        let div = n / 2;
        if div == 0 { Seq::singleton(if rem == 1 { '1' } else { '0' }) }
        else { NatToBitString(div).add(Seq::singleton(if rem == 1 { '1' } else { '0' })) }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);
    let result_nat = ModExp(x_int, y_int, z_int);
    let mut bit_string_seq = NatToBitString(result_nat);

    // Reverse the bit string if it's not '0' so that Str2Int matches the expected result
    if result_nat != 0 {
        let mut i = 0;
        let mut j = bit_string_seq.len() as int - 1;
        while i < j
            invariant
                0 <= i,
                i < bit_string_seq.len(),
                0 <= j,
                j < bit_string_seq.len(),
                i <= j + 1,
                ValidBitString(bit_string_seq),
            decreases j - i
        {
            let temp = bit_string_seq.index(i);
            bit_string_seq = bit_string_seq.update(i, bit_string_seq.index(j));
            bit_string_seq = bit_string_seq.update(j, temp);
            i = i + 1;
            j = j - 1;
        }
    }

    bit_string_seq.to_vec()
}
// </vc-code>

fn main() {}
}
