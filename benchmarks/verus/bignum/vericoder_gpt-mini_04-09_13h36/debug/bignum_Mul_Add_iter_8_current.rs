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
exec fn Nat2Vec_nat(n: usize) -> (result: Vec<char>)
  ensures ValidBitString(result@),
          Str2Int(result@) == (n as nat)
  decreases n
{
    if n == 0 {
        Vec::new()
    } else {
        let n_div2: usize = n / 2;
        let mut v = Nat2Vec_nat(n_div2);
        let old_seq: Seq<char> = v@;
        let prev_len: usize = v.len();
        let ch: char = if n % 2 == 1 { '1' } else { '0' };
        v.push(ch);
        proof {
            let len: usize = v.len();
            let len_i: int = len as int;
            let prev_len_i: int = prev_len as int;
            // length increased by 1
            assert(len == prev_len + 1);
            // last character is the pushed one
            assert(v@[len_i - 1] == ch);
            // the prefix (all but last) equals the previous sequence
            let prefix = v.get(0..(len as usize - 1)).unwrap();
            assert(prefix@ == old_seq);
            // recursive postcondition on old_seq (v before push)
            assert(Str2Int(old_seq) == (n_div2 as nat));
            // relate whole string to prefix by definition of Str2Int
            assert(Str2Int(v@) ==
                   2 * Str2Int(v@.subrange(0, len_i - 1))
                   + (if v@[len_i - 1] == '1' { 1nat } else { 0nat }));
            // combine equalities
            assert(Str2Int(v@.subrange(0, len_i - 1)) == (n_div2 as nat));
            assert((if ch == '1' { 1nat } else { 0nat }) == ((n as nat) % 2));
            assert(2 * (n_div2 as nat) + ((n as nat) % 2) == (n as nat));
        }
        v
    }
}

exec fn Nat2Vec(n: usize) -> (result: Vec<char>)
  ensures ValidBitString(result@),
          Str2Int(result@) == (n as nat)
  decreases n
{
    // call the usize-based implementation
    Nat2Vec_nat(n)
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
    let prod_usize: usize = n1 * n2;
    let res: Vec<char> = Nat2Vec_nat(prod_usize);
    proof {
        // relate runtime values to specifications
        assert((n1 as nat) == Str2Int(s1@));
        assert((n2 as nat) == Str2Int(s2@));
        // Nat2Vec_nat postcondition gives the desired equality (cast to nat)
        assert(Str2Int(res@) == (prod_usize as nat));
        assert(Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@));
    }
    res
}
// </vc-code>

fn main() {}
}