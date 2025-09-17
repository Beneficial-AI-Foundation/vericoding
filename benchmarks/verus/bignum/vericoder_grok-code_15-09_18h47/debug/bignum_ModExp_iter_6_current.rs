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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

spec fn AllZero(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

// <vc-helpers>
/* helper modified by LLM (iteration 6): Fixed type mismatches by casting indices to nat for Seq operations, and casting @ specs for Exp_int arguments to nat */
exec fn str_to_nat(s: &[char]) -> (result: u64)
    requires
        ValidBitString(s@),
        s@.len() <= 63,
    ensures
        result@ == Str2Int(s@.subrange(0, (s@.len().min(i as int) as nat))) as u64,
{
    let mut result: u64 = 0;
    let s_len = s.len();
    let mut i: usize = 0;
    while i < s_len
        invariant
            0 <= i as int && i as int <= s@.len() as int,
            result@ == Str2Int(s@.subrange(0, (s@.len().min(i as int) as nat))) as u64,
        decreases s_len - i
    {
        let ghost i_int = i as int;
        let bit: u64 = if s@[i as nat] == '1' { 1 } else { 0 };
        result = result * 2 + bit;
        i += 1;
    }
    result
}

exec fn mod_exp(x: u64, y: u64, m: u64) -> (result: u64)
    requires
        m != 0,
        y <= (u64::MAX >> 1),
        x <= (u64::MAX >> 1),
    ensures
        result@ == (Exp_int(x@ as nat, y@ as nat) % m@ as nat) as u64,
{
    let mut result: u64 = 1;
    let mut base = x;
    let mut exp = y;
    while exp != 0
        invariant
            m != 0,
            result@ <= (u64::MAX >> 1) as int,
            base@ <= (u64::MAX >> 1) as int,
            exp@ <= y@,
        decreases exp@
    {
        if exp % 2 == 1 {
            result = (((result as u128) * (base as u128)) % (m as u128)) as u64;
        }
        base = (((base as u128) * (base as u128)) % (m as u128)) as u64;
        exp = exp / 2;
    }
    result
}

exec fn nat_to_str(n: u64) -> (result: Vec<char>)
    ensures
        ValidBitString(result@),
        Str2Int(result@) == n@ as nat,
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let mut bits: Vec<char> = Vec::<char>::new();
        let mut current = n;
        while current != 0
            invariant
                current@ <= n@,
            decreases current@
        {
            if current % 2 == 1 {
                bits.push('1');
            } else {
                bits.push('0');
            }
            current = current / 2;
        }
bits.reverse();
        bits
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 6): Implementing the modular exponentiation logic using fixed helpers with correct type casts */{
    let x_nat = str_to_nat(sx);
    let y_nat = str_to_nat(sy);
    let z_nat = str_to_nat(sz);
    let result_nat = mod_exp(x_nat, y_nat, z_nat);
    let res = nat_to_str(result_nat);
    res
}
// </vc-code>

fn main() {}
}


