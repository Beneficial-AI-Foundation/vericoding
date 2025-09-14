// <vc-preamble>
function contains(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  exists j :: 0 <= j < n && a[j] == v
}

function upper_bound(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  forall j :: 0 <= j < n ==> a[j] <= v
}

function is_max(m: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  contains(m, a, n) && upper_bound(m, a, n)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unnecessary lemmas as logic is auto-provable by Dafny */
// </vc-helpers>

// <vc-spec>
method max(a: array<int>, n: int) returns (max: int)
  requires 0 < n <= a.Length;
  ensures is_max(max, a, n);
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): simplified logic and removed unnecessary helper calls */
  max := a[0];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant is_max(max, a, i)
  {
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>
