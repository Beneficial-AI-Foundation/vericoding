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
    let mut i: usize = 0;
    let mut current_max_idx: usize = 0;

    proof {
        assert(a.len() >= 1);
        assert(0 <= i && i < a.len());
        assert(0 <= current_max_idx && current_max_idx < a.len());
    }

    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            0 <= current_max_idx && current_max_idx < a.len(),
            forall|k: int| 0 <= k < i ==> a[k] <= a[current_max_idx as int],
        decreases a.len() - i
    {
        if a[i] > a[current_max_idx] {
            current_max_idx = i;
        }
        i = i + 1;
    }
    current_max_idx
}
// </vc-code>

fn main() {
}

}