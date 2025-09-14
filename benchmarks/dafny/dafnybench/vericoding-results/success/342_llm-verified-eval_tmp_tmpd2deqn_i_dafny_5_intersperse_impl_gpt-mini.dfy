

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method intersperse(numbers: seq<int>, delimiter: int) returns (interspersed: seq<int>)
    ensures |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> 
                interspersed[i] == numbers[i / 2]
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==>
                interspersed[i] == delimiter
// </vc-spec>
// <vc-code>
{
  if |numbers| == 0 {
    interspersed := [];
    return;
  }
  var n := |numbers|;
  var m := 2 * n - 1;
  var a := new int[m];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant forall j :: 0 <= j < i ==> (if j % 2 == 0 then a[j] == numbers[j / 2] else a[j] == delimiter)
  {
    if i % 2 == 0 {
      a[i] := numbers[i / 2];
    } else {
      a[i] := delimiter;
    }
    i := i + 1;
  }
  interspersed := a[..];
}
// </vc-code>

