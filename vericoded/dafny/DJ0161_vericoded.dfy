// <vc-preamble>
function SeqMax(a: seq<int>): int
    decreases |a|
{
    if |a| == 0 then
        -2147483648  // i32::MIN equivalent
    else if a[|a|-1] > SeqMax(a[..|a|-1]) then
        a[|a|-1]
    else
        SeqMax(a[..|a|-1])
}
// </vc-preamble>

// <vc-helpers>
function max2(a: int, b: int): int { if a > b then a else b }
// </vc-helpers>

// <vc-spec>
method RollingMax(numbers: array<int>) returns (result: array<int>)
    ensures result.Length == numbers.Length
    ensures forall i :: 0 <= i < numbers.Length ==> result[i] == SeqMax(numbers[..i+1])
// </vc-spec>
// <vc-code>
{
  result := new int[numbers.Length];
  var n := numbers.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] == SeqMax(numbers[..j+1])
  {
    result[i] := SeqMax(numbers[..i+1]);
    i := i + 1;
  }
}
// </vc-code>
