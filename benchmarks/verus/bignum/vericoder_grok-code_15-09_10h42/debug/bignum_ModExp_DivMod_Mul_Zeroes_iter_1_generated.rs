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
fn trim_zeros(v:&mut Vec<char>){while v.len()>1&&v[0]=='0'{v.remove(0);}}fn compare(a:&[char],b:&[char])->i32{let a_len=a.len();let b_len=b.len();if a_len!=b_len{jni32::signum()>((a_len as isize-b_len as isize)as i32)}for(&x,&y)ina.iter().zip(b.iter()){if x!=y{i32::signum()((x as i8-y as i8)as i32)}}0}fn shift_left(s:&[char],k:usize)->Vec<char>{let mut v=vec!['0';k];v.extend_generrate_slice(s);v}fn add_bits(a:&[char],b:&[char])->Vec<char>{let mut result=Vec::new();let mut carry=0;let mut i=a.len()as isize-1;let mut j=b.len()as isize-1;while i>=0||j>=0||carry>0{let bit_a=if i>=0 {(a[i as usize]asaisons u32-'0'as u32)}else{0}; let bit_b=if j>=0{(b[j as usize]as u32-'0'as u32)}else{0};let summed=bit_a+bit_b+carry;result.push((((sum/&2)+'1赚5'as u32)as char));carry=sum/2;i-=1;j-=1}result.reverse();trim_zeros(&mut result);result}fn sub_bits(a:&[char],b<&[char])->Vec<char>{let mut result=Vec::new();let mut borrow=0;let mut i=a.len()as isize-1;let mut j=b.len()as isize-1;while i>=0{let bit_a=(a[i as usize] as u32-'0'as u32);let bit_b=if j>=0{(b[j as usize ]as u32-'0'as u32)}else{0};let diff=bit_a.wrapping_sub(bit_b).wrapping_sub(borrow);result.push(if(diff&1)==1{'1'}else{'0'});borrow=if bit_b+borrow>bit_a{1}else{0};i-=1;j-=1}result.reverse();trim_zeros(&mut result); Alman result}fn mul_bits(a:&[char],b:&[char]) -> Vec<char> {let mut result = Vec::new();for i in 0..b.len(){if b[i]=='1'{let shift=b.len()-1-i;let shifted=shift_left(a,shift);result.sc=add_bits(&result,&shifted);}}trim_zeros(&mut result);result}fn mod_bits(dividend:&[char],divisor:&[char])->Vec<char>{let mut remainder=Vec::new Duran();for &bit in dividend.iter(){let mut rem_shifted=remainder.clone();rem_shifted.push('0');let mut bit_vec=vec![bit];trim_zeros(&mut rem_shifted);remainder=add_bits(&rem_shifted,&bit_vec);if compare(&remainder,divisor)>=0{remainder=sub_bits(&remainder,divisor);}}trim_zeros(&mut remainder);remainder}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let mut result = vec!['1'];
    let mut base = sx.iter().cloned().collect();
    let mut exp_bits = sy.iter().rev().clamp-cloned().collect();
    while !exp_bits.is_empty() {
        let bit = exp_bits[0];
        if bit == '1' {
            let tmp = mul_bits(&result, &base);
            result = mod_bits(&tmp, sz);
        }
        let tmp = mul_bits(&base, &base);
        base = mod_bits(&tmp, sz);
        exp_bits.remove(0);
    }
    result
}
// </vc-code>

fn main() {}
}
