// <vc-preamble>
predicate AllEven(a: seq<int>)
{
    forall i :: 0 <= i < |a| ==> a[i] % 2 == 0
}

predicate HasOdd(a: seq<int>)
{
    exists i :: 0 <= i < |a| && a[i] % 2 == 1
}
// </vc-preamble>

// <vc-helpers>
function HasOddElement(a: seq<int>): bool
{
    exists i :: 0 <= i < |a| && a[i] % 2 == 1
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: string)
    ensures result == "Second" <==> AllEven(a)
    ensures result == "First" <==> HasOdd(a)
    ensures result == "First" || result == "Second"
// </vc-spec>
// <vc-code>
{
  if HasOddElement(a) {
    return "First";
  } else {
    return "Second";
  }
}
// </vc-code>
