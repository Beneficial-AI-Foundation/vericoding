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
/* helper modified by LLM (iteration 5): Fix sequence indexing and add proper helper functions */
proof fn exp_int_base_case(x: nat) ensures Exp_int(x, 0) == 1 { }
proof fn exp_int_recursive_case(x: nat, y: nat) requires y > 0 ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat) { }
proof fn str2int_base_case() ensures Str2Int(Seq::<char>::empty()) == 0 { }
proof fn str2int_recursive_case(s: Seq<char>, c: char) requires ValidBitString(s.push(c)), c == '0' || c == '1' ensures Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }) { }
proof fn valid_bitstring_implies_chars(s: Seq<char>, i: int) requires ValidBitString(s), 0 <= i && i < s.len() as int ensures s.index(i) == '0' || s.index(i) == '1' { }
fn slice_to_vec(chars: &[char]) -> Vec<char> {
    let mut vec = Vec::new();
    vec.extend(chars.iter().cloned());
    vec
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix slice indexing and use proper usize operations */
{
    if sy.len() == 0 {
        let mut result = Vec::new();
        result.push('1');
        result
    } else {
        let y_tail = slice_to_vec(&sy[0..sy.len() - 1]);
        let last_char = sy[sy.len() - 1];
        let mut recursive_call = ModExp_DivMod_Mul_Zeroes(sx, &y_tail, sz);
        let mut temp = Vec::new();
        temp.push('0');
        temp.extend(recursive_call);
        
        proof {
            exp_int_recursive_case(Str2Int(sx@), Str2Int(sy@));
            str2int_recursive_case(y_tail@, last_char);
        }
        
        if last_char == '0' {
            temp
        } else {
            let mut x_vec = sx.to_vec();
            proof {
                valid_bitstring_implies_chars(sy@, sy.len() as int - 1);
            }
            
            while x_vec.len() < temp.len() {
                x_vec.insert(0, '0');
            }
            while temp.len() < x_vec.len() {
                temp.insert(0, '0');
            }
            
            let mut carry = '0';
            let mut result = Vec::new();
            let len = temp.len();
            
            let mut i = len;
            while i > 0 {
                i = i - 1;
                let temp_char = temp[i];
                let x_char = x_vec[i];
                
                proof {
                    valid_bitstring_implies_chars(temp@, i as int);
                    valid_bitstring_implies_chars(x_vec@, i as int);
                }
                
                let sum = (if temp_char == '1' { 1 } else { 0 }) + (if x_char == '1' { 1 } else { 0 }) + (if carry == '1' { 1 } else { 0 });
                
                match sum {
                    0 => { result.insert(0, '0'); carry = '0'; },
                    1 => { result.insert(0, '1'); carry = '0'; },
                    2 => { result.insert(0, '0'); carry = '1'; },
                    3 => { result.insert(0, '1'); carry = '1'; },
                    _ => { }
                }
            }
            
            if carry == '1' {
                result.insert(0, '1');
            }
            
            let mut mod_result = Vec::new();
            
            for j in 0..result.len() {
                let bit = result[j];
                proof {
                    valid_bitstring_implies_chars(result@, j as int);
                }
                mod_result.push(bit);
            }
            
            mod_result
        }
    }
}
// </vc-code>

fn main() {}
}
