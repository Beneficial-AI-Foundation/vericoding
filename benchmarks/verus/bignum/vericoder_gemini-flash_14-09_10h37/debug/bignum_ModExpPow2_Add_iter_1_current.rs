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

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut result_vec: Vec<char> = Vec::with_capacity(max_len + 1);
    let mut carry = 0;
    let mut i = 0;

    while i < max_len || carry > 0
        invariant
            result_vec.len() <= i + 1,
            (forall |j: int| 0 <= j && j < result_vec.len() ==> (result_vec.index(j) == '0' || result_vec.index(j) == '1')),
            Str2Int(result_vec@) == Str2Int(s1@.subrange(0, i)) + Str2Int(s2@.subrange(0, i)) + carry as nat - (if i < result_vec.len() {1} else {0}) * (if result_vec.index(i as int - 1) == '1' {2} else {0}) - (if i < result_vec.len() {1} else {0}) * (if result_vec.index(i as int - 1) == '0' {1} else {0}),
            carry == 0 || carry == 1
    {
        let bit1 = if i < len1 && s1.index(len1 - 1 - i) == '1' { 1 } else { 0 };
        let bit2 = if i < len2 && s2.index(len2 - 1 - i) == '1' { 1 } else { 0 };

        let sum = bit1 + bit2 + carry;
        carry = sum / 2;
        result_vec.insert(0, if sum % 2 == 1 { '1' } else { '0' });
        i = i + 1;
    }
    result_vec
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
        if Str2Int(sy@) == 0 {
            let mut res_vec = Vec::with_capacity(1);
            res_vec.push('1');
            return res_vec;
        }

        let sz_int = Str2Int(sz@);
        assert (sz_int > 1);

        if Str2Int(sy@) == Exp_int(2, n as nat) {
            if n == 0 {
                let mut res_vec = Vec::new();
                res_vec.push(if Str2Int(sx@) % sz_int == 0 { '0' } else { '1' });
                return res_vec;
            } else {
                let mut halfway_sy_vec = Vec::with_capacity(n as usize);
                for _ in 0..n as usize - 1 {
                    halfway_sy_vec.push('0');
                }
                halfway_sy_vec.push('1');
                
                let halfway_res_vec = ModExpPow2(sx, halfway_sy_vec.as_slice(), (n - 1) as int, sz);
                let full_sy_vec = sy.to_vec();
                let mut recursive_sx_vec = Vec::new();
                recursive_sx_vec.push('0'); // Placeholder for now, replace properly

                if Str2Int(halfway_res_vec@) == 0 {
                    recursive_sx_vec = vec!['0'];
                } else {
                    let mut temp_val = Str2Int(halfway_res_vec@);
                    while temp_val > 0 {
                        if temp_val % 2 == 1 {
                            recursive_sx_vec.insert(0, '1');
                        } else {
                            recursive_sx_vec.insert(0, '0');
                        }
                        temp_val = temp_val / 2;
                    }
                    if recursive_sx_vec.is_empty() {
                        recursive_sx_vec.push('0');
                    }
                }
                
                let squared_val = Str2Int(halfway_res_vec@) * Str2Int(halfway_res_vec@);
                let final_mod_val = squared_val % sz_int;

                let mut final_res_vec = Vec::new();
                if final_mod_val == 0 {
                    final_res_vec.push('0');
                } else {
                    let mut temp_val = final_mod_val;
                    while temp_val > 0 {
                        if temp_val % 2 == 1 {
                            final_res_vec.insert(0, '1');
                        } else {
                            final_res_vec.insert(0, '0');
                        }
                        temp_val = temp_val / 2;
                    }
                }
                if final_res_vec.is_empty() {
                    final_res_vec.push('0');
                }
                final_res_vec
            }
        } else {
            // Should not be reachable given the ensures clause
            unreachable!();
        }
    }
// </vc-code>

fn main() {}
}


