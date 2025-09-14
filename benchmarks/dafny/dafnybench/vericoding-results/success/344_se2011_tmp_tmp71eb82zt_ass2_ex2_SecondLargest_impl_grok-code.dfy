// ex2

// this was me playing around to try and get an ensures for the method 
/*predicate method check(a: array<int>, seclar:int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

// <vc-helpers>
predicate check(a: array<int>, seclar: int)
  requires a.Length > 0
  reads a
  {
    exists i :: 0 <= i < a.Length &&
      forall j :: 0 <= j < a.Length && j != i ==>
        a[i] >= a[j] &&
        seclar <= a[i] &&
        (if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
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
    seclar := a[0];
  } else {
    var max := a[0];
    var second := a[1];
    if second > max {
      var temp := max;
      max := second;
      second := temp;
    }
    var i := 2;
    while i < a.Length
      decreases a.Length - i
    {
      if a[i] > max {
        second := max;
        max := a[i];
      } else if a[i] > second {
        second := a[i];
      }
      i := i + 1;
    }
    seclar := second;
  }
}
// </vc-code>

