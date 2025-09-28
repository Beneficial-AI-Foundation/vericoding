// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
{
  /* helper modified by LLM (iteration 5): compute maximum and its position in the first x elements (requires x>0) */
  method PrefixMax(a: array<int>, x: int) returns (m: int, pos: int)
    requires 0 < x <= a.Length
    ensures 0 <= pos < x && m == a[pos] && (forall i :: 0 <= i < x ==> a[i] <= m)
  {
    pos := 0;
    m := a[0];
    var i := 1;
    while i < x
      invariant 1 <= i <= x
      invariant 0 <= pos < i
      invariant m == a[pos]
      invariant forall k :: 0 <= k < i ==> a[k] <= m
    {
      if a[i] > m {
        m := a[i];
        pos := i;
      }
      i := i + 1;
    }
  }

  /* helper modified by LLM (iteration 5): find first p >= x such that a[p] > m or reach a.Length-1 */
  method FindP(a: array<int>, x: int, m: int) returns (p: int)
    requires 0 <= x < a.Length
    ensures x <= p < a.Length && ((p < a.Length - 1) ==> (exists i :: x <= i <= p && a[i] > m)) && ((forall i :: x <= i < a.Length ==> a[i] <= m) ==> p == a.Length - 1)
  {
    p := x;
    while p < a.Length - 1 && a[p] <= m
      invariant x <= p <= a.Length - 1
      invariant forall k :: x <= k < p ==> a[k] <= m
    {
      p := p + 1;
    }
  }
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
  /* code modified by LLM (iteration 5): compute prefix maximum (use first element when x==0) and find p scanning from x */
  if x <= 0 {
    var m0, pos0 := PrefixMax(a, 1);
    var p0 := FindP(a, 0, m0);
    result := (m0, p0);
  } else {
    var m1, pos1 := PrefixMax(a, x);
    var p1 := FindP(a, x, m1);
    result := (m1, p1);
  }
}

// </vc-code>
