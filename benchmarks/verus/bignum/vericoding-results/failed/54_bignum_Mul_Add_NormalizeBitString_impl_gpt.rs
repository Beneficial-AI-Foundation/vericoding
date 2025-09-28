// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t) &&
    t.len() > 0 &&
    (t.len() > 1 ==> t[0] != '0') &&
    (valid_bit_string(s) ==> str2int(s) == str2int(t)),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
fn bits_to_int(v: &Vec<char>) -> (n: int)
  requires
    valid_bit_string(v@),
  ensures
    n == str2int(v@),
    0 <= n,
{
    let mut i: int = 0;
    let mut acc: int = 0;
    while i < v.len() as int
        invariant
            0 <= i <= v.len() as int,
            valid_bit_string(v@),
            acc == str2int(v@.subrange(0, i)),
        decreases (v.len() as int) - i
    {
        let c = v[i as usize];
        let b: int = if c == '1' { 1 } else { 0 };
        acc = 2 * acc + b;
        i = i + 1;
    }
    acc
}

fn int_to_bits(n: int) -> (res: Vec<char>)
  requires
    0 <= n,
  ensures
    valid_bit_string(res@),
    str2int(res@) == n,
{
    let mut out: Vec<char> = Vec::new();
    if n == 0 {
        out.push('0');
        return out;
    }
    let mut p: int = 1;
    while p <= n
        invariant
            1 <= p,
            0 <= n,
        decreases n - p + 1
    {
        p = p * 2;
    }
    let mut r: int = n;
    while p > 1
        invariant
            1 <= p,
            0 <= n,
            0 <= r < p,
            valid_bit_string(out@),
            n == str2int(out@) * p + r,
        decreases p
    {
        p = p / 2;
        if r >= p {
            out.push('1');
            r = r - p;
        } else {
            out.push('0');
        }
    }
    out
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) * str2int(s2@),
// </vc-spec>
// <vc-code>
{
    let n1 = bits_to_int(&s1);
    let n2 = bits_to_int(&s2);
    let prod: int = n1 * n2;
    let res_vec = int_to_bits(prod);
    res_vec
}
// </vc-code>


}

fn main() {}