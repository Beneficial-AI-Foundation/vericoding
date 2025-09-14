// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a > b then a else b }
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method SecondLargest(a:array<int>) returns (seclar:int)
requires a.Length > 0
// </vc-spec>
// <vc-code>
{
  if a.Length == 1 {
    seclar := a[0];
    return;
  }

  var largest := max(a[0], a[1]);
  var second := min(a[0], a[1]);

  var i := 2;
  while i < a.Length
    invariant 2 <= i <= a.Length
    invariant second <= largest
    invariant forall k :: 0 <= k < i ==> a[k] <= largest
    invariant exists k :: 0 <= k < i && a[k] == largest
    invariant forall k :: 0 <= k < i && a[k] < largest ==> a[k] <= second
  {
    if a[i] > largest {
      second := largest;
      largest := a[i];
    } else if a[i] < largest && a[i] > second {
      second := a[i];
    }
    i := i + 1;
  }
  seclar := second;
}
// </vc-code>
