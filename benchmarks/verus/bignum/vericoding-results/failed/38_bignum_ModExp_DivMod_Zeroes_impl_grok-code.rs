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
fn int_to_bin(n: usize) -> Vec<char>
    requires n >= 0
    decreases n
{
    /* helper modified by LLM (iteration 10): changed param from int to usize for exec compatibility */
    if n == 0 {
        vec!['0']
    } else {
        let rem = if n % 2 == 0 { '0' } else { '1' };
        let mut rest = int_to_bin(n / 2);
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
    /* code modified by LLM (iteration 10): replaced int with usize for exec types, fixed loop from len-1 downto 0, changed sy_seq to exec access */
    let len_x = sx.len();
    let mut x = 0usize;
    for i in 0..len_x {
        x = x * 2 + if sx[i] == '0' { 0 } else { 1 };
    }
    let len_z = sz.len();
    let mut mod_val = 0usize;
    for i in 0..len_z {
        mod_val = mod_val * 2 + if sz[i] == '0' { 0 } else { 1 };
    }
    let mut base = x % mod_val;
    let mut result = 1usize;
    let sy_seq = sy;
    let len = sy.len();
    let mut i = len;
    while i > 0
        invariant
            0 < i <= len
        decreases i
    {
        i -= 1;
        if sy_seq[i] == '1' {
            result = (result * base) % mod_val;
        }
        base = (base * base) % mod_val;
    }
    let res_vec = int_to_bin(result);
    res_vec
}
// </vc-code>

fn main() {}
}
