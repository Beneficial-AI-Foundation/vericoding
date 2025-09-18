// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clauses to fix termination errors */
function max(a: int, b: int): int { if a > b then a else b }

function findMax(a: array<int>, start: int, end: int): int
  requires a.Length > 0
  requires 0 <= start < end <= a.Length
  reads a
  decreases end - start
{
  if end - start == 1 then a[start]
  else max(a[start], findMax(a, start + 1, end))
}

predicate maxInRange(a: array<int>, start: int, end: int, m: int)
  requires a.Length > 0
  requires 0 <= start <= end <= a.Length
  reads a
{
  (forall i :: start <= i < end ==> a[i] <= m) &&
  (exists i :: start <= i < end && a[i] == m)
}

lemma findMaxCorrect(a: array<int>, start: int, end: int)
  requires a.Length > 0
  requires 0 <= start < end <= a.Length
  ensures maxInRange(a, start, end, findMax(a, start, end))
  decreases end - start
{
  if end - start == 1 {
    assert a[start] == findMax(a, start, end);
  } else {
    findMaxCorrect(a, start + 1, end);
    var m1 := a[start];
    var m2 := findMax(a, start + 1, end);
    assert findMax(a, start, end) == max(m1, m2);
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
  /* code modified by LLM (iteration 5): Fixed precondition error and loop invariant */
  if x == 0 {
    var p := 0;
    while p < a.Length - 1 && a[p + 1] <= a[0]
      invariant 0 <= p < a.Length
      invariant forall i :: 0 <= i <= p ==> a[i] <= a[0]
    {
      p := p + 1;
    }
    result := (a[0], p);
  } else {
    assert 0 < x < a.Length;
    var m := findMax(a, 0, x);
    findMaxCorrect(a, 0, x);
    assert maxInRange(a, 0, x, m);
    assert forall i :: 0 <= i < x ==> a[i] <= m;
    assert exists i :: 0 <= i < x && a[i] == m;
    
    var p := x;
    while p < a.Length && a[p] <= m
      invariant x <= p <= a.Length
      invariant forall i :: x <= i < p ==> a[i] <= m
      invariant p > x ==> exists i :: x <= i < p && a[i] > m
    {
      p := p + 1;
    }
    
    if p == a.Length {
      p := a.Length - 1;
    }
    
    result := (m, p);
  }
}
// </vc-code>
