method min(a : int, b : int) returns (m : int)
  ensures m == a || m == b
  ensures m <= a && m <= b
{
  assume{:axiom} false;
}
method max(a : int, b : int) returns (m : int)
  ensures m == a || m == b
  ensures m >= a && m >= b
{
  assume{:axiom} false;
}

// <vc-helpers>
predicate InRange(x: int, low: int, high: int)
{
  low <= x <= high
}

lemma EvenInSet(x: int)
  ensures x in [2, 4, 6, 8] ==> x % 2 == 0
{
  if x in [2, 4, 6, 8] {
    assert x == 2 || x == 4 || x == 6 || x == 8;
  }
}
// </vc-helpers>

// <vc-spec>
method generate_integers(a : int, b : int) returns (result: seq<int>)
  // post-conditions-start
  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] % 2 == 0
  ensures forall i : int :: i >= 0 && i < |result| ==> result[i] in [2, 4, 6, 8]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var lower := min(a, b);
  var upper := max(a, b);
  
  result := [];
  
  var candidates := [2, 4, 6, 8];
  var i := 0;
  
  while i < |candidates|
    invariant 0 <= i <= |candidates|
    invariant forall j :: 0 <= j < |result| ==> result[j] % 2 == 0
    invariant forall j :: 0 <= j < |result| ==> result[j] in [2, 4, 6, 8]
    invariant forall j :: 0 <= j < |result| ==> lower <= result[j] <= upper
  {
    var num := candidates[i];
    if lower <= num <= upper {
      result := result + [num];
      EvenInSet(num);
    }
    i := i + 1;
  }
}
// </vc-code>

