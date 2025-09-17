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
spec fn Str2Int_to_nat(s: Seq<char>) -> nat { Str2Int(s) }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);

    if y == 0 {
        return (seq_to_vec_char(nat_to_seq_char(1)));
    }

    let ym1_seq = nat_to_seq_char(y - 1);
    let res_prev = ModExp_Add_ModExpPow2(sx, &seq_to_vec_char(ym1_seq), sz);

    let intermediary_val = (x * Str2Int(res_prev@)) % z;
    return (seq_to_vec_char(nat_to_seq_char(intermediary_val)));
}

// Helper to convert `nat` to `Seq<char>`
proof fn nat_to_seq_char(n: nat) -> Seq<char>
    ensures (Str2Int(nat_to_seq_char(n)) == n)
{
    if n == 0 { return Seq::<char>::empty(); }
    let mut res = Seq::<char>::empty();
    let mut temp = n;
    while temp > 0
        invariant (Str2Int(res.reverse()@) == (n - temp))
        invariant (forall |i: int| #![trigger res.index(i)] 0 <= i && i < res.len() ==> (res.index(i) == '0' || res.index(i) == '1'))
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

// Helper to convert `Seq<char>` to `Vec<char>`
proof fn seq_to_vec_char(s: Seq<char>) -> Vec<char>
    ensures (s@ == seq_to_vec_char(s)@)
{
    let mut vec = Vec::<char>::new();
    let mut i = 0;
    while i < s.len()
        invariant (i <= s.len())
        invariant (vec@.subrange(0, i) == s@.subrange(0, i))
    {
        vec.push(s.index(i));
        i = i + 1;
    }
    return vec;
}
// </vc-code>

fn main() {}
}
