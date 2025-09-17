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
pub exec fn bits_to_nat(bs: &[char]) -> nat
  requires ValidBitString(bs@)
  ensures Str2Int(bs@) == result
{
    let mut acc: nat = 0;
    let mut i: usize = 0;
    while i < bs.len() {
        invariant ValidBitString(bs@);
        invariant acc == Str2Int(bs@.subrange(0, i as int));
        decreases bs.len() - i;
        let c = bs[i];
        // c is '0' or '1' by ValidBitString
        if c == '1' {
            acc = 2 * acc + 1;
        } else {
            acc = 2 * acc + 0;
        }
        // prove acc equals Str2Int(subrange 0..i+1)
        // by unfolding definition of Str2Int for length >= 1
        // and using the invariant for previous acc
        // (Verus will check these steps via the invariants)
        i = i + 1;
    }
    acc
}

pub exec fn nat_to_bits(mut n: nat) -> Vec<char>
  ensures ValidBitString(result@),
          Str2Int(result@) == old(n)
{
    // Represent 0 as empty vector
    if n == 0 {
        return Vec::<char>::new();
    }

    let orig = n;
    // compute highest power of two <= n
    let mut pow: nat = 1;
    // pow will grow: decreases orig - pow ensures termination
    while pow * 2 <= n {
        invariant 1 <= pow && pow <= n + 1;
        decreases orig - pow;
        pow = pow * 2;
    }

    let mut out: Vec<char> = Vec::new();
    let mut cur_pow = pow;
    let mut rem = n;
    // Process bits from most-significant (cur_pow) down to 1
    while cur_pow > 0 {
        invariant rem < cur_pow * 2;
        invariant rem >= 0;
        invariant cur_pow >= 1;
        decreases cur_pow;
        if
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
pub exec fn bits_to_nat(bs: &[char]) -> nat
  requires ValidBitString(bs@)
  ensures Str2Int(bs@) == result
{
    let mut acc: nat = 0;
    let mut i: usize = 0;
    while i < bs.len() {
        invariant ValidBitString(bs@);
        invariant acc == Str2Int(bs@.subrange(0, i as int));
        decreases bs.len() - i;
        let c = bs[i];
        // c is '0' or '1' by ValidBitString
        if c == '1' {
            acc = 2 * acc + 1;
        } else {
            acc = 2 * acc + 0;
        }
        // prove acc equals Str2Int(subrange 0..i+1)
        // by unfolding definition of Str2Int for length >= 1
        // and using the invariant for previous acc
        // (Verus will check these steps via the invariants)
        i = i + 1;
    }
    acc
}

pub exec fn nat_to_bits(mut n: nat) -> Vec<char>
  ensures ValidBitString(result@),
          Str2Int(result@) == old(n)
{
    // Represent 0 as empty vector
    if n == 0 {
        return Vec::<char>::new();
    }

    let orig = n;
    // compute highest power of two <= n
    let mut pow: nat = 1;
    // pow will grow: decreases orig - pow ensures termination
    while pow * 2 <= n {
        invariant 1 <= pow && pow <= n + 1;
        decreases orig - pow;
        pow = pow * 2;
    }

    let mut out: Vec<char> = Vec::new();
    let mut cur_pow = pow;
    let mut rem = n;
    // Process bits from most-significant (cur_pow) down to 1
    while cur_pow > 0 {
        invariant rem < cur_pow * 2;
        invariant rem >= 0;
        invariant cur_pow >= 1;
        decreases cur_pow;
        if
// </vc-code>

fn main() {}
}