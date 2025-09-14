// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindOddNumbers(arr: array<int>) returns (odd_numbers: seq<int>)
    ensures forall x :: x in odd_numbers ==> x % 2 != 0
    ensures forall i :: 0 <= i < arr.Length && arr[i] % 2 != 0 ==> arr[i] in odd_numbers
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fix the loop boundary condition and ensure all odd numbers from array are in the result sequence. */
{
  var result: seq<int> := [];
  for i := 0 to arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall x :: x in result ==> x % 2 != 0
    invariant forall k :: 0 <= k < i && arr[k] % 2 != 0 ==> arr[k] in result
  {
    if i < arr.Length && arr[i] % 2 != 0 {
      result := result + [arr[i]];
    }
  }
  return result;
}
// </vc-code>
