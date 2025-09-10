predicate ValidInput(diameters: seq<int>)
{
    |diameters| > 0 && forall i :: 0 <= i < |diameters| ==> diameters[i] > 0
}

function num_distinct(s: seq<int>): int
    ensures num_distinct(s) >= 0
    ensures num_distinct(s) <= |s|
    ensures |s| == 0 ==> num_distinct(s) == 0
    ensures |s| > 0 ==> num_distinct(s) >= 1
{
    if |s| == 0 then 0
    else if s[0] in s[1..] then num_distinct(s[1..])
    else 1 + num_distinct(s[1..])
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(diameters: seq<int>) returns (result: int)
    requires ValidInput(diameters)
    ensures result == num_distinct(diameters)
    ensures result >= 1
    ensures result <= |diameters|
// </vc-spec>
// <vc-code>
{
  var n := |diameters|;
  var i := n;
  result := 0;
  while i > 0
    invariant 0 <= i <= n
    invariant result == num_distinct(diameters[i..n])
    decreases i
  {
    var k := i - 1;
    if !(diameters[k] in diameters[k+1..n]) {
      result := result + 1;
    }
    i := k;
  }
}
// </vc-code>

