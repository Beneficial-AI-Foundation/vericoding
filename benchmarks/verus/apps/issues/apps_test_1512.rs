// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_permutation(p: Seq<int>, n: int) -> bool {
  p.len() == n && n >= 1 &&
  (forall|i: int| 0 <= i < n ==> 1 <= #[trigger] p[i] <= n) &&
  (forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] p[i] != #[trigger] p[j])
}

spec fn count_records(s: Seq<int>) -> int {
  if s.len() == 0 { 0 }
  else { 1 + count_records_from_index(s, 1, s[0]) }
}

spec fn count_records_after_removal(p: Seq<int>, to_remove: int) -> int {
  let filtered = Seq::new((p.len() - 1) as nat, |i: int| 
    if index_of(p, to_remove) <= i { p[i + 1] } else { p[i] });
  count_records(filtered)
}
spec fn count_records_from_index(s: Seq<int>, idx: int, max_so_far: int) -> int
  decreases s.len() - idx
{
  if idx >= s.len() { 0 }
  else if s[idx] > max_so_far { 
    1 + count_records_from_index(s, idx + 1, s[idx])
  } else { 
    count_records_from_index(s, idx + 1, max_so_far)
  }
}

spec fn index_of(s: Seq<int>, elem: int) -> int {
  choose|i: int| 0 <= i < s.len() && s[i] == elem
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, p: Vec<i8>) -> (result: i8)
  requires 
    valid_permutation(p@.map(|i, x: i8| x as int), n as int)
  ensures 
    1 <= result as int <= n as int,
    p@.map(|i, x: i8| x as int).contains(result as int),
    {
      let p_int = p@.map(|i, x: i8| x as int);
      forall|x: int| p_int.contains(x) ==> count_records_after_removal(p_int, result as int) >= count_records_after_removal(p_int, x)
    },
    {
      let p_int = p@.map(|i, x: i8| x as int);
      forall|x: int| p_int.contains(x) && count_records_after_removal(p_int, x) == count_records_after_removal(p_int, result as int) ==> result as int <= x
    }
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}