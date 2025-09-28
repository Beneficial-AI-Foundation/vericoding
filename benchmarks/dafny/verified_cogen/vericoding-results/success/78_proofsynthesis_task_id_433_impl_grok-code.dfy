// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsGreater(arr: array<int>, number: int) returns (result: bool)
    ensures result == (forall i :: 0 <= i < arr.Length ==> number > arr[i])
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 2): Fixed duplicate result variable by assigning to the returns parameter instead of var declaration. */
result := true;
var i: int := 0;
while i < arr.Length
  invariant 0 <= i <= arr.Length
  invariant result == (forall j :: 0 <= j < i ==> number > arr[j])
{
  if arr[i] >= number { result := false; }
  i := i + 1;
}
}
// </vc-code>
