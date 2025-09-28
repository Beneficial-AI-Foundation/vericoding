// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn string_value(s: Seq<char>, w: Seq<int>) -> int
  decreases s.len()
{
  if s.len() == 0 { 0 }
  else {
    let char_index = (s.last() as int) - ('a' as int);
    string_value(s.drop_last(), w) + s.len() * w[char_index]
  }
}

spec fn append_value(start_pos: int, count: int, max_val: int) -> int
  decreases count
{
  if count <= 0 { 0 }
  else { (start_pos + count) * max_val + append_value(start_pos, count - 1, max_val) }
}

spec fn max_value(w: Seq<int>) -> int
  decreases w.len()
{
  if w.len() <= 1 { w[0] }
  else if w[0] >= max_value(w.subrange(1, w.len() as int)) { w[0] }
  else { max_value(w.subrange(1, w.len() as int)) }
}

spec fn valid_input(s: Seq<char>, k: int, w: Seq<int>) -> bool
{
  w.len() == 26 && 
  k >= 0 && 
  s.len() <= 1000 && 
  k <= 1000 && 
  (forall|i: int| 0 <= i < w.len() ==> #[trigger] w[i] >= 0 && #[trigger] w[i] <= 1000) &&
  (forall|i: int| 0 <= i < s.len() ==> 'a' <= #[trigger] s[i] && #[trigger] s[i] <= 'z')
}
// </vc-preamble>

// <vc-helpers>
fn runtime_string_value(s: &Vec<char>, w: &Vec<i8>) -> int
    requires
        w.len() == 26,
        (forall|i: int| 0 <= i && i < s@.len() ==> 'a' <= s@[i] && s@[i] <= 'z'),
    ensures
        result as int == string_value(s@, w@.map(|i, x| x as int)),
{
    let n = s.len() as int;
    let seqw = w@.map(|i, x| x as int);
    let mut i: int = 0;
    let mut acc: int = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            acc == string_value(s@.subrange(0, i as nat), seqw),
        decreases n - i
    {
        let c = s[i as nat];
        let idx = (c as int) - ('a' as int);
        acc = acc + (i + 1) * seqw@[idx];
        i = i + 1;
    }
    acc
}

fn runtime_max(w: &Vec<i8>) -> int
    requires w.len() > 0,
    ensures result as int == max_value(w@.map(|i, x| x as int)),
{
    let seqw = w@.map(|i, x| x as int);
    let n = seqw.len() as int;
    let mut i: int = 1;
    let mut m: int = seqw@[0];
    while i < n
        invariant
            0 <= i && i <= n,
            m == max_value(seqw.subrange(0, i as nat)),
        decreases n - i
    {
        let v = seqw@[i];
        if v > m {
            m = v;
        }
        i = i + 1;
    }
    m
}

fn runtime_append_value(start_pos: int, count: int, max_val: int) -> int
    requires count >= 0,
    ensures result as int == append_value(start_pos, count, max_val),
{
    let n = count;
    let mut i: int = 0;
    let mut acc: int = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            acc == append_value(start_pos, i, max_val),
        decreases n - i
    {
        acc = acc + (start_pos + i + 1) * max_val;
        i = i + 1;
    }
    acc
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, k: i8, w: Vec<i8>) -> (result: i8)
  requires valid_input(s@, k as int, w@.map(|i, x| x as int))
  ensures result as int == string_value(s@, w@.map(|i, x| x as int)) + append_value(s@.len() as int, k as int, max_value(w@.map(|i, x| x as int)))
// </vc-spec>
// <vc-code>
{
    let strv = runtime_string_value(&s, &w);
    let maxv = runtime_max(&w);
    let addv = runtime_append_value(s.len() as int, k as int, maxv);
    let res_i: int = strv + addv;
    let res: i8 = res_i as i8;
    res
}
// </vc-code>


}

fn main() {}