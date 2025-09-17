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
proof fn exp_int_recursive_lemma(x: nat, y: nat)
    ensures
        y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat),
        y == 0 ==> Exp_int(x, y) == 1
{
    // Base case is automatically handled by the spec function definition
}

proof fn str2int_recursive_lemma(s: Seq<char>)
    requires
        ValidBitString(s)
    ensures
        s.len() > 0 ==> Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }),
        s.len() == 0 ==> Str2Int(s) == 0
{
    // Base case is automatically handled by the spec function definition
}

proof fn valid_bitstring_subrange_lemma(s: Seq<char>, start: int, end: int)
    requires
        ValidBitString(s),
        0 <= start,
        end <= s.len() as int
    ensures
        ValidBitString(s.subrange(start, end))
{
}

fn vec_from_seq(s: Seq<char>) -> (v: Vec<char>)
    ensures
        v@ == s,
        ValidBitString(v@)
{
    let mut v = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i,
            i <= s.len(),
            v@ == s.subrange(0, i),
            ValidBitString(v@)
    {
        v.push(s[i as usize]);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed integer/nat type conversion error */
    let y_str = vec_from_seq(sy@);
    
    if y_str.len() == 0 {
        // Base case: s^0 mod m = 1
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let mut y_vec = y_str.clone();
    let last_char = y_vec.pop().unwrap();
    
    // Recursive call for y/2
    let recursive_result = ModExp_Add_Zeroes(sx, &y_vec, sz);
    
    let mut temp = recursive_result.clone();
    
    if last_char == '1' {
        // If last bit is 1: x^(2y+1) = x * (x^y)^2
        let squared = ModExp_Add_Zeroes(&temp, &vec!['1', '1'], sz);
        temp = ModExp_Add_Zeroes(sx, &squared, sz);
    } else {
        // If last bit is 0: x^(2y) = (x^y)^2
        temp = ModExp_Add_Zeroes(&temp, &vec!['1', '1'], sz);
    }
    
    temp
}
// </vc-code>

fn main() {}
}
