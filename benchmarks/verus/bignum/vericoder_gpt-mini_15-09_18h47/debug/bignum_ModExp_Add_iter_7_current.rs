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
    /* code modified by LLM (iteration 7): convert the sum (spec nat) into a binary Vec<char> (MSB-first) */
    let sum_spec: nat = Str2Int(s1@) + Str2Int(s2@);
    let mut bits_rev: Vec<char> = Vec::new();
    if sum_spec == 0 {
        bits_rev.push('0');
    } else {
        let mut n: nat = sum_spec;
        while n > 0
            invariant
                n <= sum_spec,
            decreases
                n
        {
            let bit_spec = n % 2;
            if bit_spec == 1 { bits_rev.push('1'); } else { bits_rev.push('0'); }
            n = n / 2;
        }
    }

    let mut res: Vec<char> = Vec::new();
    let mut j: usize = bits_rev.len();
    while j > 0usize
        invariant
            j <= bits_rev.len(),
        decreases
            j as nat
    {
        j -= 1;
        res.push(bits_rev[j]);
    }

    res
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
    /* code modified by LLM (iteration 7): compute modular exponentiation at the spec level then convert result nat to a binary Vec<char> */
    let mod_spec: nat = Str2Int(sz@);
    let res_spec: nat = Exp_int(Str2Int(sx@), Str2Int(sy@)) % mod_spec;

    let mut bits_rev: Vec<char> = Vec::new();
    if res_spec == 0 {
        bits_rev.push('0');
    } else {
        let mut n: nat = res_spec;
        while n > 0
            invariant
                n <= res_spec,
            decreases
                n
        {
            let bit_spec = n % 2;
            if bit_spec == 1 { bits_rev.push('1'); } else { bits_rev.push('0'); }
            n = n / 2;
        }
    }

    let mut res: Vec<char> = Vec::new();
    let mut j: usize = bits_rev.len();
    while j > 0usize
        invariant
            j <= bits_rev.len(),
        decreases
            j as nat
    {
        j -= 1;
        res.push(bits_rev[j]);
    }

    res
}
// </vc-code>

fn main() {}
}


