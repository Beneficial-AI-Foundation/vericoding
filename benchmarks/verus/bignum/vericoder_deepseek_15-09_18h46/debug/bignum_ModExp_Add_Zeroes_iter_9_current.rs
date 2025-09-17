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
/* helper modified by LLM (iteration 9): fix to_nat_from_int function signature and implementation */
fn to_nat_from_int(x: int) -> nat
    requires x >= 0
    ensures to_nat_from_int(x) == x as nat
{
    if x == 0 {
        0
    } else {
        let prev = to_nat_from_int(x - 1);
        prev + 1
    }
}

proof fn exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

proof fn exp_rec(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

proof fn str2int_empty()
    ensures Str2Int(Seq::empty()) == 0
{
}

proof fn str2int_rec(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
{
}

proof fn valid_bitstring_subrange(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start <= end <= s.len() as int
    ensures ValidBitString(s.subrange(start, end))
{
}

proof fn valid_bitstring_append(s: Seq<char>, c: char)
    requires ValidBitString(s), c == '0' || c == '1'
    ensures ValidBitString(s.push(c))
{
}

proof fn exp_mod_property(x: nat, y: nat, m: nat)
    requires m > 1
    ensures Exp_int(x, y) % m == Exp_int(x % m, y) % m
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): fix ghost code conversion and remove problematic casting */
{
    proof {
        exp_mod_property(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
    }
    let x_mod = Str2Int(sx@) % Str2Int(sz@);
    let y_val = Str2Int(sy@);
    let exp_result_ghost = Exp_int(x_mod, y_val) % Str2Int(sz@);
    
    let exp_result: int = exp_result_ghost as int;
    
    let mut temp = exp_result;
    let mut result_bits = Vec::new();
    
    if temp == 0 {
        result_bits.push('0');
    } else {
        while temp > 0
            invariant
                temp >= 0,
                ValidBitString(result_bits@),
                Str2Int(result_bits@) == (exp_result - temp) as nat
            decreases temp
        {
            if temp % 2 == 1 {
                result_bits.push('1');
            } else {
                result_bits.push('0');
            }
            temp = temp / 2;
        }
        result_bits.reverse();
    }
    
    result_bits
}
// </vc-code>

fn main() {}
}
