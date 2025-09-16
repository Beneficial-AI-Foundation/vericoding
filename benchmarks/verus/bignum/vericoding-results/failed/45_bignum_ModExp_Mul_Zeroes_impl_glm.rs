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
exec fn nat_to_binary(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    if n == 0 {
        vec!['0']
    } else {
        let mut res = Vec::new();
        let mut num = n;
        while num > 0
            invariant num >= 0,
            decreases num
        {
            if num % 2 == 0 {
                res.push('0');
            } else {
                res.push('1');
            }
            num = num / 2;
        }
        res.reverse();
        res
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        // Base case: x^0 = 1
        nat_to_binary(1 % {
            let mut res = 0;
            for i in 0..sz.len()
            {
                res = res * 2;
                if sz[i] == '1' {
                    res += 1;
                }
            }
            res
        })
    } else {
        // Recursive case
        let prefix = &sy[0..sy.len() - 1];
        let last_bit = sy[sy.len() - 1];
        
        // Compute x^(y/2) mod m
        let half_result = ModExp_Mul_Zeroes(sx, prefix, sz);
        
        // Convert half_result back to a natural number
        let half_value = {
            let mut res = 0;
            for i in 0..half_result.len()
            {
                res = res * 2;
                if half_result[i] == '1' {
                    res += 1;
                }
            }
            res
        };
        
        // Convert sz to a natural number
        let m = {
            let mut res = 0;
            for i in 0..sz.len()
            {
                res = res * 2;
                if sz[i] == '1' {
                    res += 1;
                }
            }
            res
        };
        
        // Convert sx to a natural number
        let x = {
            let mut res = 0;
            for i in 0..sx.len()
            {
                res = res * 2;
                if sx[i] == '1' {
                    res += 1;
                }
            }
            res
        };
        
        // Compute the final result
        let result = if last_bit == '0' {
            (half_value * half_value) % m
        } else {
            ((half_value * half_value) % m * x) % m
        };
        
        // Convert result back to binary string
        nat_to_binary(result)
    }
}
// </vc-code>

fn main() {}
}
