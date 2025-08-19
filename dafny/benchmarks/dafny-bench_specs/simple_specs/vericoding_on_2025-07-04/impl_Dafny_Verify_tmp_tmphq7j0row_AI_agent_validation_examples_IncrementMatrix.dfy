//ATOM

method Cube(n: nat) returns (c: nat) 
  ensures c == n * n * n
{
  /* code modified by LLM (iteration 1): Fixed implementation to compute cube correctly */
  c := n * n * n;
}

//ATOM

function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}

//ATOM

method Max(a: array<nat>) returns (m: int)
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
  ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
  /* code modified by LLM (iteration 1): Fixed implementation to find maximum element */
  if a.Length == 0 {
    m := 0;
  } else {
    m := a[0];
    var k := 1;
    while k < a.Length
      invariant 1 <= k <= a.Length
      invariant forall i :: 0 <= i < k ==> a[i] <= m
      invariant exists i :: 0 <= i < k && m == a[i]
    {
      if a[k] > m {
        m := a[k];
      }
      k := k + 1;
    }
  }
}

method IncrementMatrix(a: array2<int>)
  modifies a
  ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
  /* code modified by LLM (iteration 1): Added implementation to increment all matrix elements */
  var i := 0;
  while i < a.Length0
    invariant 0 <= i <= a.Length0
    invariant forall r, c :: 0 <= r < i && 0 <= c < a.Length1 ==> a[r,c] == old(a[r,c]) + 1
    invariant forall r, c :: i <= r < a.Length0 && 0 <= c < a.Length1 ==> a[r,c] == old(a[r,c])
  {
    var j := 0;
    while j < a.Length1
      invariant 0 <= j <= a.Length1
      invariant forall r, c :: 0 <= r < i && 0 <= c < a.Length1 ==> a[r,c] == old(a[r,c]) + 1
      invariant forall c :: 0 <= c < j ==> a[i,c] == old(a[i,c]) + 1
      invariant forall c :: j <= c < a.Length1 ==> a[i,c] == old(a[i,c])
      invariant forall r, c :: i < r < a.Length0 && 0 <= c < a.Length1 ==> a[r,c] == old(a[r,c])
    {
      a[i,j] := a[i,j] + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}