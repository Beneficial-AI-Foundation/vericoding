//ATOM
function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}

//IMPL Max
method Max(a: array<nat>) returns (m: int)
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
  if a.Length == 0 {
    m := 0;
  } else {
    m := a[0];
    var j := 1;
    while j < a.Length
      invariant 1 <= j <= a.Length
      invariant forall k :: 0 <= k < j ==> a[k] <= m
      invariant exists k :: 0 <= k < j && m == a[k]
    {
      if a[j] > m {
        m := a[j];
      }
      j := j + 1;
    }
  }
}