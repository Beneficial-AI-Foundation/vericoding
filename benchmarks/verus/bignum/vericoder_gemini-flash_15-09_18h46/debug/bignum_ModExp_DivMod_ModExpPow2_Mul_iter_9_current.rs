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
/* helper modified by LLM (iteration 8): Addressed compilation error in `nat_to_char_vec_spec` by changing the type of `digit` to `nat` for `Str2Int` and then converting it to `char` when adding to the sequence. */
spec fn nat_to_char_vec_spec(n: nat) -> (result: Seq<char>)
    ensures
        ValidBitString(result),
        Str2Int(result) == n,
        result.len() >= 1 || n == 0
{
    if n == 0 { Seq::new(1, |i| '0') } else { 
        let mut num = n;
        let mut s: Seq<char> = Seq::empty();
        while num > 0
            invariant
                ValidBitString(s),
                todo!(), // Str2Int(s.reverse()) + (num / 10 * Exp_int(10, s.len())) as nat == n,
            decreases num
        {
            let digit = (num % 10);
            s = Seq::singleton(if digit == 0 { '0' } else if digit == 1 { '1' } else if digit == 2 { '2' } else if digit == 3 { '3' } else if digit == 4 { '4' } else if digit == 5 { '5' } else if digit == 6 { '6' } else if digit == 7 { '7' } else if digit == 8 { '8' } else { '9' }).add(s);
            num = num / 10;
        }
        if s.len() == 0 { Seq::singleton('0') } else { s }
     }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 8): The error message indicates that `exponent = (exponent / 2) as nat;` is causing a compilation error. `exponent` is already declared as `nat`, so the `as nat` cast is redundant and incorrect when `exponent / 2` also results in a `nat`. Removing the `as nat` cast resolves this. */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);

    let mut result_val: nat = 1;
    let mut base: nat = x_val % z_val;
    let mut exponent: nat = y_val;

    proof {
        assert((result_val * Exp_int(base, exponent)) % z_val == Exp_int(x_val, y_val) % z_val);
    }

    while exponent > 0
        invariant
            z_val > 1,
            (result_val * Exp_int(base, exponent)) % z_val == Exp_int(x_val, y_val) % z_val,
        decreases exponent
    {
        if exponent % 2 == 1 {
            result_val = (result_val * base) % z_val;
        }
        base = (base * base) % z_val;
        exponent = (exponent / 2);
    }

    nat_to_char_vec_spec(result_val).to_vec()
}
// </vc-code>

fn main() {}
}
