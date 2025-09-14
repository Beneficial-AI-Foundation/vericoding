// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function initialMaxRec(a: array<int>, x: int): (int, int)
  requires a.Length > 0 && 0 <= x && x < a.Length
  reads a
  ensures var (m, p) := initialMaxRec(a, x);
          x <= p && p < a.Length &&
          (forall i :: 0 <= i < x ==> a[i] <= m) &&
          (exists i :: 0 <= i < x && a[i] == m) &&
          ((p < a.Length - 1) ==> (exists i :: x <= i <= p && a[i] > m)) &&
          ((forall i :: x <= i < a.Length ==> a[i] <= m) ==> p == a.Length - 1)
{
  if x == 0 then
    (a[0], 0)
  else
    var prevRec := initialMaxRec(a, x-1);
    var prevM := prevRec.0;
    if a[x] > prevM then
      (a[x], x)
    else if prevP < a.Length - 1 && (forall i :: x <= i < a.Length ==> a[i] <= prevM) then
      (prevM, a.Length - 1)
    else
      prevRec
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
  /* code modified by LLM (iteration 5): directly handle base case and ensure x>=0 */
  if x < 0 {
    x := 0;
  }
  result := initialMaxRec(a, x);
}
// </vc-code>
