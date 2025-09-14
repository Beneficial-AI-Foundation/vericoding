// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Max returns the larger of two integers */
function Max(a: int, b: int): int { if a >= b then a else b }

/* helper modified by LLM (iteration 2): PrefixMax returns the maximum of the first n elements of a sequence */
function PrefixMax(s: seq<int>, n: int): int
  requires n > 0 && |s| >= n
  ensures forall i :: 0 <= i < n ==> s[i] <= PrefixMax(s,n)
  ensures exists i :: 0 <= i < n && s[i] == PrefixMax(s,n)
{
  if n == 1 then s[0] else var t := PrefixMax(s[1..], n-1); if s[0] >= t then s[0] else t
}
// </vc-helpers>

// <vc-spec>
method OnlineMax(a: array<int>, x: int) returns (result: (int, int))
    requires
        a.Length > 0 &&
        x < a.Length
    ensures
        var (m, p) := result;
        x <= p && p < a.Length &&
        (forall i :: 0 <= i < x ==> a[i] <= m) &&
        (exists i :: 0 <= i < x && a[i] == m) &&
        ((p < a.Length - 1) ==> (exists i :: x <= i <= p && a[i] > m)) &&
        ((forall i :: x <= i < a.Length ==> a[i] <= m) ==> p == a.Length - 1)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterate to compute maximum of a[0..x-1] with i starting at 0 and maintain conditional invariants */
  var m := 0;
  var i := 0;
  while i < x
    invariant 0 <= i <= x
    invariant i > 0 ==> forall k :: 0 <= k < i ==> a[k] <= m
    invariant i > 0 ==> exists k :: 0 <= k < i && a[k] == m
  {
    if i == 0 {
      m := a[0];
    } else {
      if a[i] > m {
        m := a[i];
      }
    }
    i := i + 1;
  }
  result := (m, a.Length - 1);
}
// </vc-code>
