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
/* helper modified by LLM (iteration 3): fixed type annotations and index conversions */
proof fn lemma_str2int_rec(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index((s.len() - 1) as int) == '1' { 1nat } else { 0nat })
{
}

spec fn char_to_nat(c: char) -> nat
{
    if c == '1' { 1nat } else { 0nat }
}

proof fn lemma_char_index_type(s: Seq<char>, i: int)
    requires 0 <= i && i < s.len() as int
    ensures s.index(i) == '1' || s.index(i) == '0'
{
}

proof fn lemma_subrange_conversion(s: Seq<char>, start: int, end: int)
    requires 0 <= start && start <= end && end <= s.len() as int
    ensures 0 <= end - start && end - start <= s.len()
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed type conversion issues, indexing, and arithmetic operations */
{
    let m = Str2Int(sz@) as int;
    let mut x_val = (Str2Int(sx@) as int) % m;
    let mut result = 1;
    
    let mut i = 0int;
    while i < sy@.len() as int
        invariant
            result == (Exp_int(Str2Int(sx@), Str2Int(sy@.subrange(i, sy@.len() as int))) as int) % m,
            i <= sy@.len() as int
        decreases (sy@.len() as int) - i
    {
        let bit = sy@.index(i);
        result = if bit == '1' {
            (result * x_val) % m
        } else {
            result
        };
        x_val = (x_val * x_val) % m;
        i += 1;
    }
    
    let mut res_vec = Vec::new();
    let mut temp = result;
    if temp == 0 {
        res_vec.push('0');
    } else {
        while temp > 0
            invariant temp >= 0
            decreases temp
        {
            if temp % 2 == 0 {
                res_vec.push('0');
            } else {
                res_vec.push('1');
            }
            temp = temp / 2;
        }
        res_vec.reverse();
    }
    
    res_vec
}
// </vc-code>

fn main() {}
}
