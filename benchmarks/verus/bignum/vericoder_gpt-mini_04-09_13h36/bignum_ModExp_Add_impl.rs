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
proof fn exp_mul2(n: nat)
  ensures Exp_int(2, n + 1) == 2 * Exp_int(2, n)
{
    if n == 0 {
        assert(Exp_int(2, 0) == 1);
        assert(Exp_int(2, 1) == 2 * Exp_int(2, 0));
    } else {
        exp_mul2((n - 1) as nat);
        assert(Exp_int(2, n + 1) == 2 * Exp_int(2, n));
    }
}

spec fn LeStr2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        LeStr2Int(prefix) + (if s.index(s.len() as int - 1) == '1' { Exp_int(2, (s.len() as nat) - 1) } else { 0nat })
    }
}

spec fn LowBits(s: Seq<char>, k: nat) -> nat
  recommends ValidBitString(s)
  decreases k
{
    if k as int >= s.len() as int {
        Str2Int(s)
    } else {
        LeStr2Int(s.subrange(s.len() as int - (k as int), s.len() as int))
    }
}

fn int_to_vec(n: nat) -> Vec<char>
  decreases n
  ensures Str2Int(result@) == n
  ensures ValidBitString(result@)
{
    if n == 0 {
        Vec::new()
    } else {
        let q = n / 2;
        let r = n % 2;
        let mut v = int_to_vec(q);
        if r == 1 {
            v.push('1');
        } else {
            v.push('0');
        }
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let mut v1: nat = 0;
    let mut i: usize = 0;
    while i < s1.len() {
        invariant i <= s1.len();
        invariant ValidBitString(s1@);
        invariant v1 == Str2Int(s1@.subrange(0, i as int));
        let b = if s1@.index(i as int) == '1' { 1 } else { 0 };
        v1 = 2 * v1 + b;
        i += 1;
    }

    let mut v2: nat = 0;
    let mut j: usize = 0;
    while j < s2.len() {
        invariant j <= s2.len();
        invariant ValidBitString(s2@);
        invariant v2 == Str2Int(s2@.subrange(0, j as int));
        let b = if s2@.index(j as int) == '1' { 1 } else { 0 };
        v2 = 2 * v2 + b;
        j += 1;
    }

    let total = v1 + v2;
    let res = int_to_vec(total);
    res
}
// </vc-code>

fn main() {}
}