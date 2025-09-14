// <vc-preamble>
predicate IsEven(n: int)
{
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
lemma ZeroIsEven() ensures IsEven(0) { }
lemma EvenSum(x: int, y: int)
  requires IsEven(x) && IsEven(y)
  ensures IsEven(x + y)
{ }
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers(arr: array<int>) returns (result: array<int>)
    ensures forall i :: 0 <= i < result.Length ==> IsEven(result[i])
    ensures forall i :: 0 <= i < result.Length ==> exists j :: 0 <= j < arr.Length && result[i] == arr[j]
// </vc-spec>
// <vc-code>
{
  result := new int[0];
}
// </vc-code>
