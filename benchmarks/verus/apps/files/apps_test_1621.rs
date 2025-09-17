// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn string_value(s: Seq<char>, w: Seq<int>) -> int
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    let char_index = (s[s.len() - 1] as int) - ('a' as int);
    string_value(s.subrange(0, s.len() - 1), w) + s.len() * w[char_index]
  }
}

spec fn append_value(start_pos: int, count: int, max_val: int) -> int
  decreases count
{
  if count == 0 {
    0
  } else {
    (start_pos + count) * max_val + append_value(start_pos, count - 1, max_val)
  }
}

spec fn max_value(w: Seq<int>) -> int
  decreases w.len()
{
  if w.len() == 1 {
    w[0]
  } else if w[0] >= max_value(w.subrange(1, w.len() as int)) {
    w[0]
  } else {
    max_value(w.subrange(1, w.len() as int))
  }
}

spec fn valid_input(s: Seq<char>, k: int, w: Seq<int>) -> bool {
  w.len() == 26 && 
  k >= 0 && 
  s.len() <= 1000 && 
  k <= 1000 && 
  (forall|i: int| 0 <= i < w.len() ==> 0 <= w[i] <= 1000) &&
  (forall|i: int| 0 <= i < s.len() ==> 'a' <= s[i] <= 'z')
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(s: Seq<char>, k: int, w: Seq<int>) -> (result: i32)
  requires 
    valid_input(s, k, w),
    w.len() == 26,
    forall|i: int| 0 <= i < s.len() ==> 'a' <= s[i] <= 'z',
    w.len() > 0
// </vc-spec>
// <vc-code>
{
  // impl-start
  assume(false);
  0
  // impl-end
}
// </vc-code>


}

fn main() {}