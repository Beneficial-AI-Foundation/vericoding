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
/* helper modified by LLM (iteration 3): Fixed compilation errors by using BigNat instead of nat for exec functions and using while loops instead of for loops to avoid nat/int in exec */
exec fn str_to_nat(s: &[char]) -> (result: BigNat)
    requires ValidBitString(s@)
    ensures BigNat::spec_eq(result@, Str2Int(s@))
{
    let mut result = BigNat::zero();
    let s_len = s.len();
    let mut i: usize = 0;
    while i < s_len
        invariant
            0 <= i as int && i as int <= s@.len() as int,
            BigNat::spec_eq(result@, Str2Int(s@.subrange(0, s@.len().min(i as int)))),
        decreases s_len - i
    {
        let temp = if s@[i as int] == '1' { BigNat::one() } else { BigNat::zero() };
        result = result * (BigNat::one() + BigNat::one()) + temp;
        i += 1;
    }
    result
}

exec fn mod_exp(x: BigNat, y: BigNat, m: BigNat) -> (result: BigNat)
    requires m != BigNat::zero()
    ensures BigNat::spec_eq(result@, Exp_int(x@, y@) % m@)
{
    let mut result = BigNat::one();
    let mut base = x;
    let mut exp = y;
    while !exp.is_zero()
    invariant
        m != BigNat::zero(),
    decreases exp@ if exp@ > 0 else 0
    {
        if exp.clone() % (BigNat::one() + BigNat::one()) == BigNat::one() {
            result = (result * base.clone()) % m.clone();
        }
        base = (base.clone() * base.clone()) % m.clone();
        exp = exp / BigNat::from(2);
    }
    result
}

exec fn nat_to_str(n: BigNat) -> (result: Vec<char>)
    ensures
        ValidBitString(result@),
        BigNat::spec_eq(n@, Str2Int(result@))
{
    if n == BigNat::zero() {
        Vec::<char>::new()
    } else {
        let mut bits: Vec<char> = Vec::<char>::new();
        let mut current = n;
        while !current.is_zero()
            invariant current@ >= 0
            decreases current@
        {
            if current.clone() % (BigNat::one() + BigNat::one()) == BigNat::one() {
                bits.push('1');
            } else {
                bits.push('0');
            }
            current = current / BigNat::from(2);
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
{
  /* code modified by LLM (iteration 3): Updated to handle input slices as parameters */
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


