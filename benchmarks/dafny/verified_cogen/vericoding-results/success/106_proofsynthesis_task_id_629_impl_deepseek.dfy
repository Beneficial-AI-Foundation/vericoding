// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed function declaration syntax */
function IsEven(n: int): bool {
  n % 2 == 0
}

lemma EvenPreservedInSequence(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures s[i] % 2 == 0 ==> s[i] in s
{
}
// </vc-helpers>

// <vc-spec>
method FindEvenNumbers(arr: array<int>) returns (even_numbers: seq<int>)
    ensures |even_numbers| <= arr.Length
    ensures forall i :: 0 <= i < |even_numbers| ==> even_numbers[i] % 2 == 0
    ensures forall x :: x in even_numbers ==> x in arr[..]
    ensures forall i :: 0 <= i < arr.Length && arr[i] % 2 == 0 ==> arr[i] in even_numbers
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed method implementation */
{
  var index := 0;
  even_numbers := [];
  
  while index < arr.Length
    invariant 0 <= index <= arr.Length
    invariant |even_numbers| <= index
    invariant forall j :: 0 <= j < |even_numbers| ==> even_numbers[j] % 2 == 0
    invariant forall x :: x in even_numbers ==> x in arr[..]
    invariant forall j :: 0 <= j < index && arr[j] % 2 == 0 ==> arr[j] in even_numbers
  {
    if IsEven(arr[index]) {
      even_numbers := even_numbers + [arr[index]];
    }
    index := index + 1;
  }
}
// </vc-code>
