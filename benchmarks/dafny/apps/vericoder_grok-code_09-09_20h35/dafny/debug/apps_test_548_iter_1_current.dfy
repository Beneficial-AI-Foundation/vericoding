predicate AllEven(a: seq<int>)
{
    forall i :: 0 <= i < |a| ==> a[i] % 2 == 0
}

predicate HasOdd(a: seq<int>)
{
    exists i :: 0 <= i < |a| && a[i] % 2 == 1
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: string)
    ensures result == "Second" <==> AllEven(a)
    ensures result == "First" <==> HasOdd(a)
    ensures result == "First" || result == "Second"
// </vc-spec>
// <vc-code>
{
  var i: int := 0;
  var all_even: bool := true;
  while i < |a| && all_even
    invariant 0 <= i <= |a|
    invariant all_even ==> forall k :: 0 <= k < i ==> a[k] % 2 == 0
  {
    if a[i] % 2 == 0 {
      i := i + 1;
    } else {
      all_even := false;
    }
  }
  if all_even {
    result := "Second";
  } else {
    result := "First";
  }
}
// </vc-code>

