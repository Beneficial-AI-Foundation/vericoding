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
exec fn Nat2Vec_nat(n: nat) -> (result: Vec<char>)
  ensures ValidBitString(result@),
          Str2Int(result@) == n
  decreases n
{
    if n == 0 {
        Vec::new()
    } else {
        let n_div2: nat = n / 2;
        let mut v = Nat2Vec_nat(n_div2);
        let old_seq: Seq<char> = v@;
        let prev_len: int = v.len() as int;
        let ch: char = if n % 2 == 1 { '1' } else { '0' };
        v.push(ch);
        proof {
            let len: int = v.len() as int;
            // length increased by 1
            assert(len == prev_len + 1);
            // last character is the pushed one
            assert(v@[len - 1] == ch);
            // the prefix (all but last) equals the previous sequence
            let prefix = v.get(0..(len as usize - 1)).unwrap();
            assert(prefix@ == old_seq);
            // recursive postcondition on old_seq (v before push)
            assert(Str2Int(old_seq) == n_div2);
            // relate whole string to prefix by definition of Str2Int
            assert(Str2Int(v@) ==
                   2 * Str2Int(v@.subrange(0, len - 1))
                   + (if v@[len - 1] == '1' { 1nat } else { 0nat }));
            // combine equalities
            assert(Str2Int(v@.subrange(0, len - 1)) == n_div2);
            assert((if ch == '1' { 1nat } else { 0nat }) == (n % 2));
            assert(2 * n_div2 + (n % 2) == n);
        }
        v
    }
}

exec fn Nat2Vec(n: usize) -> (result: Vec<char>)
  ensures ValidBitString(result@),
          Str2Int(result@) == (n as nat)
  decreases n
{
    // call the nat-based implementation
    Nat2Vec_nat(n as nat)
}

exec fn Slice2Nat(s: &[char]) -> (result: usize)
  requires ValidBitString(s@)
  ensures (result as nat) == Str2Int(s@)
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let k: usize = s.len();
        // s.len() > 0 here
        assert(k >= 1);
        let ch: char = s[k - 1];
        let bit: usize = if ch == '1' { 1 } else { 0 };
        let prefix = s.get(0..k - 1).unwrap();
        let n_prefix = Slice2Nat(prefix);
        proof {
            let k_int: int = k as int;
            // relate runtime indexing to sequence view
            assert((&s)@[k_int - 1] == ch);
            // prefix@ equals s@.subrange(0, k_int - 1)
            assert(prefix@ == s@.subrange(0, k_int - 1));
            // by recursive postcondition (cast)
            assert((n_prefix as nat) == Str2Int(prefix@));
            // relation of whole string to prefix by Str2Int definition
            assert(Str2Int(s@) ==
                   2 * Str2Int(s@.subrange(0, k_int - 1))
                   + (if s@[k_int - 1] == '1' { 1nat } else { 0nat }));
            // combine equalities
            assert(2 * (n_prefix as nat) + (if ch == '1' { 1nat } else { 0nat })
                   == Str2Int(s@));
            assert((if ch == '1' { 1usize } else { 0usize }) == bit);
            // cast Str2Int(s@) to usize is valid in this proof line (relating nat to usize)
            // use the established equalities to conclude the returned value relation
            assert(2usize * n_prefix + bit == (Str2Int(s@) as usize));
        }
        2 * n_prefix + bit
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1: usize = Slice2Nat(s1);
    let n2: usize = Slice2Nat(s2);
    let prod_nat: nat = (n1 as nat) * (n2 as nat);
    let res: Vec<char> = Nat2Vec_nat(prod_nat);
    proof {
        // relate runtime values to specifications
        assert((n1 as nat) == Str2Int(s1@));
        assert((n2 as nat) == Str2Int(s2@));
        // Nat2Vec_nat postcondition gives the desired equality
        assert(Str2Int(res@) == prod_nat);
        assert(Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@));
    }
    res
}
// </vc-code>

fn main() {}
}