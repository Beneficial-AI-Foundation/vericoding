function Power(base: int, exponent: int): int
    requires exponent >= 0
{
    if exponent == 0 then 1
    else base * Power(base, exponent-1)
}

// <vc-helpers>
// The duplicate Power function is removed.
// The original Power function is in the PREAMBLE and can be used directly.
// </vc-helpers>

// <vc-spec>
method PowerOfListElements(l: seq<int>, n: int) returns (result: seq<int>)
    requires n >= 0
    ensures |result| == |l|
    ensures forall i :: 0 <= i < |l| ==> result[i] == Power(l[i], n)
// </vc-spec>
// <vc-code>
{
  var result_elements := new int[|l|];
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall j :: 0 <= j < i ==> result_elements[j] == Power(l[j], n)
  {
    result_elements[i] := Power(l[i], n);
    i := i + 1;
  }
  return result_elements[..];
}
// </vc-code>

