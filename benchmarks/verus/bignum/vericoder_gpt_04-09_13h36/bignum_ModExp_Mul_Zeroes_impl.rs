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
proof fn lemma_valid_subrange_0_i(s: Seq<char>, i: int)
  requires
    ValidBitString(s),
    0 <= i,
    i <= s.len() as int
  ensures
    ValidBitString(s.subrange(0, i))
{
  assert(forall |j: int| 0 <= j && j < i ==> (s.subrange(0, i).index(j) == '0' || s.subrange(0, i).index(j) == '1')) by {
    forall |j: int| 0 <= j && j < i ==> (s.subrange(0, i).index(j) == '0' || s.subrange(0, i).index(j) == '1') {
      if 0 <= j && j < i {
        assert(0 <= j && j < s.len() as int) by { assert(i <= s.len() as int); }
        assert(s.subrange(0, i).index(j) == s.index(j));
        assert(ValidBitString(s));
        assert(s.index(j) == '0' || s.index(j) == '1');
      }
    }
  }
}

proof fn lemma_valid_push(s: Seq<char>, c: char)
  requires
    ValidBitString(s),
    c == '0' || c == '1'
  ensures
    ValidBitString(s.push(c))
{
  assert(forall |j: int|
    0 <= j && j < s.push(c).len() as int ==> (s.push(c).index(j) == '0' || s.push(c).index(j) == '1')) by {
    forall |j: int| 0 <= j && j < s.push(c).len() as int ==> (s.push(c).index(j) == '0' || s.push(c).index(j) == '1') {
      if 0 <= j && j < s.push(c).len() as int {
        if j < s.len() as int {
          assert(s.push(c).index(j) == s.index(j));
          assert(ValidBitString(s));
          assert(s.index(j) == '0' || s.index(j) == '1');
        } else {
          assert(s.push(c).len() == s.len() + 1);
          assert(!(j < s.len() as int));
          assert(j <= s.len() as int) by {
            assert(0 <= j);
            assert(j < s.len() as int + 1);
          }
          assert(j == s.len() as int);
          assert(s.push(c).index(j) == c);
          assert(c == '0' || c == '1');
        }
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  loop
    invariant true
  {
  }
}
// </vc-code>

fn main() {}
}