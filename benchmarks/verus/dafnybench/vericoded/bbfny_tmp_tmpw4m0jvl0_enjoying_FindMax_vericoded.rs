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
    let mut best: usize = 0;
    let mut j: usize = 1;

    while j < a.len()
        invariant
            0 <= best < a.len(),
            1 <= j,
            j <= a.len(),
            forall|k: int| 0 <= k < j as int ==> a[k] <= a[best as int]
        decreases (a.len() - j as int) as nat
    {
        if a[j] > a[best] {
            best = j;
        } else {
            assert(a[j as int] <= a[best as int]);
        }
        j = j + 1;
    }

    assert(j == a.len());
    best
}
// </vc-code>

fn main() {
}

}