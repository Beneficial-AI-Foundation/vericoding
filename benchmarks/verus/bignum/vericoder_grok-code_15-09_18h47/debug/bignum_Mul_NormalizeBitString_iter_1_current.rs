use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
recommends ValidBitString(s)
decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
spec fn make_binary(n: nat) -> Seq<char>
    requires n >= 0
    decreases n
    ensures
        ValidBitString(result),
        Str2Int(result) == n
{
    if n == 0 {
        Seq::new(1, '0')
    } else if n == 1 {
        Seq::new(1, '1')
    } else if n % 2 == 0 {
        make_binary(n / 2) + Seq::new(1, '0')
    } else {
        make_binary(n / 2) + Seq::new(1, '1')
    }
}

exec fn make_vec(n: nat) -> (r: Vec<char>)
    requires n >= 0
    decreases n
    ensures r@ == make_binary(n)
{
    if n == 0 {
        vec!['0']
    } else if n == 1 {
        vec!['1']
    } else if n % 2 == 0 {
        let mut rest = make_vec(n / 2);
        rest.push('0');
        rest
    } else {
        let mut rest = make_vec(n / 2);
        rest.push('1');
        rest
    }
}

spec fn compute_int(s: Seq<char>) -> nat
    requires ValidBitString(s)
    decreases s.len()
    ensures compute_int(s) == Str2Int(s)
{
    if s.is_empty() {
        0nat
    } else {
        2nat * compute_int(s.subrange(0, s.len() - 1)) + if s.last() == '1' { 1nat } else { 0nat }
    }
}

exec fn get_int(s: &[char]) -> (u: nat)
    requires ValidBitString(s@)
    decreases s.len()
    ensures compute_int(s@) == u
{
    if s.is_empty() {
        0nat
    } else {
        let rest_int = get_int(&s[0..s.len()-1]);
        let bit = if s[s.len()-1] == '1' {1nat} else {0nat};
        2nat * rest_int + bit
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1 = get_int(s1);
    let n2 = get_int(s2);
    let n = n1 * n2;
    make_vec(n)
}
// </vc-code>

fn main() {}
}
