// ex2

// this was me playing around to try and get an ensures for the method 
/*predicate method check(a: array<int>, seclar:int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

// <vc-helpers>
ghost predicate IsMax(a: array<int>, m: int)
  requires a.Length > 0
  reads a
{
  m in a[..] && forall i :: 0 <= i < a.Length ==> a[i] <= m
}

ghost predicate IsSecondLargest(a: array<int>, seclar: int)
  requires a.Length > 0
  reads a
{
  exists max :: IsMax(a, max) && 
    seclar <= max &&
    (forall i :: 0 <= i < a.Length ==> 
      (a[i] == max || a[i] <= seclar))
}
// </vc-helpers>

// <vc-spec>
method SecondLargest(a:array<int>) returns (seclar:int)
requires a.Length > 0
//ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
// </vc-spec>
// <vc-code>
{
  if a.Length == 1 {
    return a[0];
  }
  
  var max := a[0];
  var sec := a[0];
  var i := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant max in a[0..i]
    invariant sec in a[0..i]
    invariant forall j :: 0 <= j < i ==> a[j] <= max
    invariant sec <= max
    invariant forall j :: 0 <= j < i ==> (a[j] == max || a[j] <= sec)
  {
    if a[i] > max {
      sec := max;
      max := a[i];
    } else if a[i] > sec {
      sec := a[i];
    }
    i := i + 1;
  }
  
  return sec;
}
// </vc-code>

