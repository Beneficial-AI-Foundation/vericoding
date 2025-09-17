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
/* helper modified by LLM (iteration 5): This section is left empty as helper functions are either directly defined in `vc-code` or not necessary here to fix the reported compilation error. */
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected the `invariant` syntax for the `while` loop within `nat_to_seq_char_recursive` by enclosing the entire `forall` statement in curly braces. The `vc-code` section now contains the method body for `ModExp_Add_ModExpPow2` as well as the definitions for helper functions `nat_to_seq_char_recursive` and `seq_to_vec_char`. */
{
    let x_nat = Str2Int(sx@);
    let y_nat = Str2Int(sy@);
    let z_nat = Str2Int(sz@);

    if y_nat == 0 {
        return seq_to_vec_char(nat_to_seq_char_recursive(1));
    }

    // Recursive step for ModExp(x, y, z) = x * ModExp(x, y-1, z) % z
    // The decrease argument for the recursion should be y_nat.  This is implicit through sy.len() > 0
    let ym1_seq_char = nat_to_seq_char_recursive((y_nat - 1) as nat);
    let prev_res: Vec<char> = ModExp_Add_ModExpPow2(sx, &seq_to_vec_char(ym1_seq_char), sz);
    let prev_res_nat = Str2Int(prev_res@);

    let intermediary_val = (x_nat * prev_res_nat) % z_nat;
    return seq_to_vec_char(nat_to_seq_char_recursive(intermediary_val));
}


macro_rules! array_to_vec {
    ($arr:expr) => [{
        let mut vec = Vec::new();
        for item in $arr {
            vec.push(item.clone());
        }
        vec
    }];
}

exec fn nat_to_seq_char_recursive(n: nat) -> (s: Seq<char>)
    ensures (Str2Int(s) == n),
    decreases n
{
    if n == 0 {
        return Seq::<char>::empty();
    }
    let mut res = Seq::<char>::empty();
    let mut temp = n;
    while temp > 0
        invariant {
            Str2Int(res.reverse()) + Str2Int(nat_to_seq_char_recursive(temp)) * Exp_int(2, res.len() as nat) == n
        },
        invariant forall |i: int| #![trigger res.index(i)] 0 <= i && i < res.len() ==> (res.index(i) == '0' || res.index(i) == '1')
        decreases temp
    {
        if temp % 2 == 1 {
            res = res.push('1');
        } else {
            res = res.push('0');
        }
        temp = temp / 2;
    }
    return res.reverse();
}

exec fn seq_to_vec_char(s: Seq<char>) -> (v: Vec<char>)
    ensures (v@ == s)
{
    let mut vec = Vec::<char>::new();
    let mut i = 0;
    while i < s.len()
        invariant i <= s.len(),
        invariant vec@.subrange(0, i) == s.subrange(0, i)
        decreases s.len() - i
    {
        vec.push(s.index(i));
        i = i + 1;
    }
    return vec;
}
// </vc-code>

fn main() {}
}
