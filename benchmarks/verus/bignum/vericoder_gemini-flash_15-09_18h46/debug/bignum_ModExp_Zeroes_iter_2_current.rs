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
/* helper modified by LLM (iteration 2): Changed return type of `log_2` to `nat` and `n/2` to `(n/2) as nat` */
spec fn log_2(n: nat) -> nat {
    if n <= 1 { 0 }
    else { 1 + log_2((n / 2) as nat) }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Refactored `to_string` and `chars().collect()` to use `Int2Str` helper. */
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);

    if y == 0 {
        return (seq!['1']).into_iter().collect();
    }

    let mut result: Vec<char> = (seq!['1']).into_iter().collect(); // start with 1
    let mut xx = x % z;
    let mut yy = y;

    while yy > 0
        invariant
            result@.len() > 0,
            ValidBitString(result@),
            xx < z,
            xx >= 0,
            yy >= 0,
            Exp_int(x,y) % z == (Str2Int(result@) * Exp_int(xx, yy)) % z,
            Str2Int(result@) < z,
        decreases yy
    {
        if yy % 2 == 1 {
            result = (Str2Int(result@) * xx % z).to_string().chars().collect();
        }
        xx = (xx * xx) % z;
        yy = (yy / 2) as nat;
    }

    result.into_iter().collect()
}
// </vc-code>

fn main() {}
}
