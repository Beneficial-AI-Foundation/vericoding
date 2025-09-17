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
fn int_to_bin(n: int) -> Vec<char>
    requires n >= 0int
    decreases n as nat
{
    /* helper modified by LLM (iteration 8): added proper int suffixes to literals for type matching */
    if n == 0int {
        vec!['0']
    } else {
        let rem = if n % 2int == 0int { '0' } else { '1' };
        let mut rest = int_to_bin(n / 2int);
        rest.push(rem);
        rest
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 8): fixed all compilation errors by adding int/nat suffixes, changed indexing to int, fixed loop variables and decreases */
    let len_x: int = sx@.len() as int;
    let mut x: int = 0int;
    for i in 0int..len_x {
        x = x * 2int + if sx[i as usize] == '0' {0int} else {1int};
    }
    let len_z: int = sz@.len() as int;
    let mut mod_val: int = 0int;
    for i in 0int..len_z {
        mod_val = mod_val * 2int + if sz[i as usize] == '0' {0int} else {1int};
    }
    let mut base: int = x % mod_val;
    let mut result: int = 1int;
    let sy_seq = sy@;
    let len = sy@.len() as int;
    let mut i = len - 1int;
    while i >= 0int
        invariant
            0int <= i <= len,
        decreases i as nat
    {
        if sy_seq@[i] == '1' {
            result = (result * base) % mod_val;
        }
        base = (base * base) % mod_val;
        i = i - 1int;
    }
    let res_vec = int_to_bin(result);
    return res_vec;
}
// </vc-code>

fn main() {}
}
