// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added helper function to check even numbers */
function IsEven(x: int): bool { x % 2 == 0 }
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers(arr: array<int>) returns (even_numbers: seq<int>)
    ensures |even_numbers| <= arr.Length
    ensures forall i :: 0 <= i < |even_numbers| ==> even_numbers[i] % 2 == 0
    ensures forall x :: x in even_numbers ==> x in arr[..]
    ensures forall i :: 0 <= i < arr.Length && arr[i] % 2 == 0 ==> arr[i] in even_numbers
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Implemented loop with invariants to prove postconditions */
{
  var result := [];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant |result| <= i
    invariant forall j :: 0 <= j < |result| ==> result[j] % 2 == 0
    invariant forall j :: 0 <= j < |result| ==> result[j] in arr[0..i]
    invariant forall j :: 0 <= j < i && arr[j] % 2 == 0 ==> arr[j] in result
  {
    if IsEven(arr[i]) 
    {
      result := result + [arr[i]];
    }
    i := i + 1;
  }
  even_numbers := result;
}
// </vc-code>
