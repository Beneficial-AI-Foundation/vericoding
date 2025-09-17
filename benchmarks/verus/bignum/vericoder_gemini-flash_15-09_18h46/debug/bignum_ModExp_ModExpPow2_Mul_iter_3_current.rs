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
/* helper modified by LLM (iteration 2): Removed verus_code_gen_test_ModExp prefix from traits in pow_properties_generic to fix compilation. */
proof fn pow_properties_generic<F: S, V: S>(x: F, y: V, modVal: F)
    requires
        modVal > 1
    ensures
        (x * y) % modVal == ((x % modVal) * (y % modVal)) % modVal,
        (x + y) % modVal == ((x % modVal) + (y % modVal)) % modVal
{
}
spec fn convert_nat_to_char_vec(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 { Seq::new().push('0') }
    else
    {
        let mut result = Seq::new();
        let mut num = n;
        while num > 0
            invariant
                num >= 0
        {
            if num % 2 == 0 {
                result = result.push('0');
            } else {
                result = result.push('1');
            }
            num = num / 2;
        }
        result
    }
}

proof fn convert_nat_to_char_vec_properties(n: nat)
    ensures (n > 0 ==> Str2Int(convert_nat_to_char_vec(n).reverse()) == n),
            (n == 0 ==> Str2Int(convert_nat_to_char_vec(n).reverse()) == 0),
            (n > 0 ==> forall |i: int| 0 <= i && i < convert_nat_to_char_vec(n).len() ==> (convert_nat_to_char_vec(n)@.index(i) == '0' || convert_nat_to_char_vec(n)@.index(i) == '1')),
            (convert_nat_to_char_vec(0)@.len() == 1)
{
    if n > 0 {
        let mut result = Seq::new();
        let mut num = n;
        let mut i = 0;
        let mut s_val = 0;

        while num > 0
            invariant
                num >= 0,
                forall |j: int| 0 <= j && j < result.len() ==> (result.index(j) == '0' || result.index(j) == '1'),
                s_val == Str2Int(result),
                (num * Exp_int(2, i as nat) + s_val) == n,
                i == result.len()
        {
            if num % 2 == 0 {
                result = result.push('0');
            } else {
                result = result.push('1');
            }
            num = num / 2;
            i = i + 1;
            s_val = Str2Int(result);
        }
        assert(Str2Int(result.reverse()) == n);
        assert(ValidBitString(convert_nat_to_char_vec(n)@));
    }
}

proof fn Str2Int_plus_bound(orig_sy: Seq<char>, sy: Seq<char>, i: int, sum: nat)
    requires
        ValidBitString(orig_sy),
        sy.len() == orig_sy.len() - i,
        sum == Str2Int(orig_sy.subrange(i as int, orig_sy.len() as int)),
        0 <= i,
        i <= orig_sy.len()
    ensures
        sum < Exp_int(2, (orig_sy.len() - i) as nat) + 1,
        sum >= 0
    decreases sy.len()
{
    if sy.len() == 0 {
        assert(sum == 0);
    } else {
        let first_bit_val = if sy.index(0) == '1' { 1nat } else { 0nat };
        let new_sy = sy.subrange(1, sy.len() as int);
        let new_sum = Str2Int(new_sy);
        Str2Int_plus_bound(orig_sy, new_sy, i + 1, new_sum);
        assert(sum == Exp_int(2, (sy.len() - 1) as nat) * first_bit_val + new_sum);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Replaced `vassert` with `assert` because `assert` is the correct function for assertions within code blocks. */
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);

    let mut result: nat = 1;
    let mut base: nat = x;
    let mut exponent: nat = y;

    while exponent > 0
        invariant
            result > 0,
            exponent >= 0,
            Exp_int(x, y) % z == (result * Exp_int(base, exponent)) % z,
            base > 0,
            z > 1,
            (ValidBitString(sx@) && ValidBitString(sy@) && ValidBitString(sz@))
        decreases exponent
    {
        if exponent % 2 == 1 {
            result = (result * base) % z;
        }
        base = (base * base) % z;
        exponent = exponent / 2;
    }

    convert_nat_to_char_vec_properties(result);
    let final_res_seq = convert_nat_to_char_vec(result).reverse();
    
    assert(ValidBitString(final_res_seq));
    assert(Str2Int(final_res_seq) == result);

    final_res_seq.to_vec()
}
// </vc-code>

fn main() {}
}
