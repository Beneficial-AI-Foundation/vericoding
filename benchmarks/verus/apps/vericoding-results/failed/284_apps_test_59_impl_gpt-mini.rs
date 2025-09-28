// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>, p: Seq<char>) -> bool {
    n >= 2 &&
    a.len() == n &&
    p.len() == n - 1 &&
    (forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i] == '0' || #[trigger] p[i] == '1') &&
    (forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= n) &&
    a.to_set() =~= Set::new(|i: int| 1 <= i <= n)
}

spec fn max_up_to(a: Seq<int>, i: int) -> int
    recommends 0 <= i < a.len()
    decreases i when i >= 0
{
    if i == 0 { 
        a[0] 
    } else if i > 0 && a[i] > max_up_to(a, i-1) { 
        a[i] 
    } else if i > 0 { 
        max_up_to(a, i-1) 
    } else {
        a[0]
    }
}

spec fn can_sort(n: int, a: Seq<int>, p: Seq<char>) -> bool
    recommends valid_input(n, a, p)
{
    forall|i: int| 0 <= i < n - 1 ==> 
        (#[trigger] p[i] == '0' ==> max_up_to(a, i) <= i + 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): proves max_up_to value is within valid range */
proof fn max_up_to_in_range(a: Seq<int>, i: int)
    requires
        0 <= i < a.len(),
        (forall|k: int| 0 <= k < a.len() ==> 1 <= a[k] <= a.len()),
    ensures
        1 <= max_up_to(a, i) <= a.len(),
{
    if i == 0 {
        assert(max_up_to(a, 0) == a[0]);
        assert(1 <= a[0] <= a.len());
    } else {
        max_up_to_in_range(a, i - 1);
        if a[i] > max_up_to(a, i - 1) {
            assert(max_up_to(a, i) == a[i]);
            assert(1 <= a[i] <= a.len());
        } else {
            assert(max_up_to(a, i) == max_up_to(a, i - 1));
            assert(1 <= max_up_to(a, i - 1) <= a.len());
        }
    }
}

/* helper modified by LLM (iteration 5): unrolling step for max_up_to across adjacent indices */
proof fn max_up_to_step(a: Seq<int>, i: int)
    requires
        0 <= i < a.len() - 1,
    ensures
        if a[i + 1] > max_up_to(a, i) { a[i + 1] } else { max_up_to(a, i) } == max_up_to(a, i + 1),
{
    if a[i + 1] > max_up_to(a, i) {
        assert(max_up_to(a, i + 1) == a[i + 1]);
    } else {
        assert(max_up_to(a, i + 1) == max_up_to(a, i));
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>, p: Vec<char>) -> (result: String)
    requires
        valid_input(n as int, a@.map(|i, x| x as int), p@),
    ensures
        result@ == seq!['Y', 'E', 'S'] || result@ == seq!['N', 'O'],
        (result@ == seq!['Y', 'E', 'S']) <==> can_sort(n as int, a@.map(|i, x| x as int), p@),
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): iterate vector, maintain cur=max_up_to, check p== '0' condition and prove with invariants */
  let n_usize: usize = n as usize;
  let mut idx: usize = 0;
  let mut cur: i8 = a[0];
  let mut ok: bool = true;

  while idx < n_usize - 1
      invariant
          0 <= idx as int,
          idx as int <= (n as int) - 1,
          (cur as int) == max_up_to(a@.map(|i, x| x as int), idx as int),
          (forall|k: int| 0 <= k < idx as int ==> (p@@[k] != '0' || max_up_to(a@.map(|i, x| x as int), k) <= k + 1)),
      decreases
          (n as int) - (idx as int)
  {
      if p[idx] == '0' && (cur as i32) > (idx as i32 + 1) {
          ok = false;
          break;
      }

      let nextv: i8 = a[idx + 1];
      if nextv > cur {
          cur = nextv;
      }

      idx += 1;
  }

  proof {
      let a_seq: Seq<int> = a@.map(|i, x| x as int);
      let p_seq: Seq<char> = p@;

      if ok {
          assert(idx as int >= (n as int) - 1);
          assert(idx as int <= (n as int) - 1);
          assert(idx as int == (n as int) - 1);
          assert(forall|k: int| 0 <= k < n as int - 1 ==> (p_seq@[k] != '0' || max_up_to(a_seq, k) <= k + 1));
      } else {
          assert(0 <= idx as int);
          assert(idx as int < (n as int) - 1);
          assert(p_seq@[idx as int] == '0');
          assert((cur as int) > idx as int + 1);
          assert((cur as int) == max_up_to(a_seq, idx as int));
          assert(max_up_to(a_seq, idx as int) > idx as int + 1);
      }
  }

  if ok {
      String::from("YES")
  } else {
      String::from("NO")
  }
}

// </vc-code>


}

fn main() {}