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
        let mut vec_s1 = s1.to_vec();
        vec_s1.reverse();
        let mut vec_s2 = s2.to_vec();
        vec_s2.reverse();

        let mut result = Vec::new();
        let mut carry = 0nat;
        let mut i = 0;
        let max_len = if vec_s1.len() > vec_s2.len() { vec_s1.len() } else { vec_s2.len() };

        while i < max_len || carry > 0
            invariant
                carry.is_nat(),
                result@.len() == i,
                ValidBitString(result@),
                (Str2Int(result@.reverse()) + carry) == (if i >= vec_s1.len() { 0nat } else { Str2Int(vec_s1.subrange(i as int, vec_s1.len() as int).reverse()) }) + (if i >= vec_s2.len() { 0nat } else { Str2Int(vec_s2.subrange(i as int, vec_s2.len() as int).reverse()) }) + Str2Int(s1@) + Str2Int(s2@),
                forall |j: int| 0 <= j && j < i ==> 
                    (result@[j] == '0' || result@[j] == '1'),
                ValidBitString(s1@), ValidBitString(s2@)
            decreases max_len - i
        {
            let digit1 = if i < vec_s1.len() && vec_s1[i] == '1' { 1nat } else { 0nat };
            let digit2 = if i < vec_s2.len() && vec_s2[i] == '1' { 1nat } else { 0nat };

            let sum = digit1 + digit2 + carry;

            result.push(if sum % 2 == 1 { '1' } else { '0' });
            carry = sum / 2;
            i = i + 1;
        }
        result.reverse();
        if result.len() == 0 { Vec::from(['0']) } else { result }
    }
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
        let mut product = Vec::from(['0']);

        let mut vec_s1 = s1.to_vec();
        vec_s1.reverse(); 
        let mut s1_val = 0nat;
        let mut power_of_2 = 1nat;
        for i_s1 in 0..vec_s1.len() {
            if vec_s1[i_s1] == '1' {
                s1_val = s1_val + power_of_2;
            }
            power_of_2 = power_of_2 * 2;
        }

        let mut vec_s2 = s2.to_vec();
        vec_s2.reverse();
        let mut shifted_s1 = if s1.len() == 0 { Vec::from(['0']) } else { s1.to_vec() };

        let mut k = 0;
        while k < vec_s2.len()
            invariant
                ValidBitString(product@),
                ValidBitString(shifted_s1@),
                ValidBitString(s1@),
                ValidBitString(s2@),
                Str2Int(product@) == Str2Int(s1@) * Str2Int(s2@.subrange(0, k as int)),
                Str2Int(shifted_s1@) == Str2Int(s1@) * Exp_int(2, k as nat)
            decreases vec_s2.len() - k
        {
            if vec_s2[k] == '1' {
                product = Add(&product, &shifted_s1);
            }
            shifted_s1 = ShiftLeft(&shifted_s1);
            k = k + 1;
        }

        product
    }
// </vc-code>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
        let x_int = Str2Int(sx@);
        let y_int = Str2Int(sy@);
        let z_int = Str2Int(sz@);

        if y_int == 0 {
            return u2b(1);
        }

        let mut base_vec = sx.to_vec();
        let mut exp_int = y_int;
        let mut result_vec = u2b(1);

        while exp_int > 0
            invariant
                ValidBitString(base_vec@),
                ValidBitString(result_vec@),
                ValidBitString(sx@),
                ValidBitString(sy@),
                ValidBitString(sz@),
                exp_int.is_nat(),
                y_int.is_nat(),
                z_int > 1,
                Str2Int(result_vec@) * Exp_int(Str2Int(base_vec@), exp_int) % z_int == Exp_int(x_int, y_int) % z_int,
                Str2Int(base_vec@) < z_int * 2,
                Str2Int(result_vec@) < z_int * 2
            decreases exp_int
        {
            if exp_int % 2 == 1 {
                result_vec = Mul(&result_vec, &base_vec);
                result_vec = Modulo(&result_vec, &sz);
            }
            base_vec = Mul(&base_vec, &base_vec);
            base_vec = Modulo(&base_vec, &sz);
            exp_int = exp_int / 2;
        }
        result_vec
    }
// </vc-code>

fn main() {}
}


