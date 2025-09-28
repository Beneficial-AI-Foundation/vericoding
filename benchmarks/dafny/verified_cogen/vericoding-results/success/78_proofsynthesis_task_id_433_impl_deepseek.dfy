// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma HelperLemma(arr: array<int>, number: int, i: int)
  requires 0 <= i <= arr.Length
  ensures (forall j :: 0 <= j < i ==> number > arr[j]) == (
    if i == 0 then true
    else (forall j :: 0 <= j < i-1 ==> number > arr[j]) && number > arr[i-1]
  )
{
  if i > 0 {
    HelperLemma(arr, number, i-1);
  }
}
// </vc-helpers>

// <vc-spec>
method IsGreater(arr: array<int>, number: int) returns (result: bool)
    ensures result == (forall i :: 0 <= i < arr.Length ==> number > arr[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := true;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant result == (forall j :: 0 <= j < i ==> number > arr[j])
  {
    if number <= arr[i] {
      result := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
