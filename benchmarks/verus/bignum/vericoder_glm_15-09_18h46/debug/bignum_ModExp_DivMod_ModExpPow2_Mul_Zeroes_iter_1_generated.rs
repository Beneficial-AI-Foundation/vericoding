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
exec fn str2int_exec(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let last_char = s[s.len()-1];
        let last_val = if last_char == '1' { 1 } else { 0 };
        let head = &s[0..s.len()-1];
        let head_val = str2int_exec(head);
        2 * head_val + last_val
    }
}

exec fn int2str_exec(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@) && Str2Int(res@) == n
    decreases n
{
    if n == 0 {
        vec!['0']
    } else {
        let last_bit = if n % 2 == 1 { '1' } else { '0' };
        let head = int2str_exec(n / 2);
        if head.len() == 1 && head[0] == '0' {
            if last_bit == '0' {
                vec!['0']
            } else {
                vec!['1']
            }
        } else {
            let mut res = head;
            res.push(last_bit);
            res
        }
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
{
    if sy.len() == 1 {
        let x_nat = str2int_exec(sx);
        let z_nat = str2int_exec(sz);
        let b = sy[0];
        let exp_nat = if b == '0' { 0 } else { 1 };
        let result_nat = if exp_nat == 0 { 1 } else { x_nat } % z_nat;
        int2str_exec(result_nat)
    } else {
        let sy_head = &sy[0..sy.len()-1];
        let last_bit = sy[sy.len()-1];
        let head_result = ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx, sy_head, sz);
        let head_result_nat = str2int_exec(&head_result);
        let z_nat = str2int_exec(sz);
        let temp = (head_result_nat * head_result_nat) % z_nat;
        let x_nat = str2int_exec(sx);
        let factor = if last_bit == '1' { x_nat % z_nat } else { 1 };
        let result_nat = (temp * factor) % z_nat;
        int2str_exec(result_nat)
    }
}
// </vc-code>

fn main() {}
}
