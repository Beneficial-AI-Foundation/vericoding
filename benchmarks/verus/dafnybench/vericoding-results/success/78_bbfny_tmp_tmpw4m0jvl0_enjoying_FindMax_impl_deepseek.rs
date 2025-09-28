use vstd::prelude::*;

verus! {

// shenanigans going through the dafny tutorial




spec fn max(a: int, b: int) -> int
{
  if a > b { a } else { b }
}
fn testing()
{
  assume(false);
}

spec fn abs(x: int) -> int
{
  if x < 0 { -x } else { x }
}


spec fn fib(n: nat) -> nat
    decreases n
{
  if n == 0 { 0 }
  else if n == 1 { 1 }
  else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

spec fn sorted(a: &[int]) -> bool
{
  forall|j: int, k: int| 0 <= j < k < a.len() ==> a[j] < a[k]
}

// <vc-helpers>
proof fn lemma_max_property(a: int, b: int, m: int)
    requires m == max(a, b)
    ensures a <= m && b <= m && (m == a || m == b)
{
}

proof fn lemma_forall_max(a: Seq<int>, i: int, j: int)
    requires
        0 <= i < a.len(),
        0 <= j < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[i],
    ensures a[j] <= a[i]
{
}
// </vc-helpers>

// <vc-spec>
fn find_max(a: &[int]) -> (i: usize)
    requires 
        a.len() >= 1
    ensures 
        0 <= i < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[i as int]
// </vc-spec>
// <vc-code>
{
  let mut idx: usize = 0;
  let mut current_max: int = a[0];
  
  let mut n: usize = 1;
  while n < a.len()
    invariant
        0 <= idx < a.len(),
        n <= a.len(),
        forall|k: int| 0 <= k < n ==> a[k] <= a[idx as int],
        current_max == a[idx as int]
    decreases a.len() - n
  {
    if a[n] > current_max {
        current_max = a[n];
        idx = n;
    }
    n = n + 1;
  }
  idx
}
// </vc-code>

fn main() {
}

}