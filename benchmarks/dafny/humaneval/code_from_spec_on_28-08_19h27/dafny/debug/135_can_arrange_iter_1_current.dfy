// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: method can_arrange(arr: seq<int>) returns (pos: int)
Create a function which returns the largest index of an element which is not greater than or equal to the element immediately preceding it. If no such element exists then return -1.
*/
// </vc-description>

// <vc-spec>
method can_arrange(arr: seq<int>) returns (pos: int)
  ensures pos == -1 ==> forall i :: 1 <= i < |arr| ==> arr[i] >= arr[i-1]
  ensures pos != -1 ==> 1 <= pos < |arr| && arr[pos] < arr[pos-1]
  ensures pos != -1 ==> forall i :: pos < i < |arr| ==> arr[i] >= arr[i-1]
// </vc-spec>
// <vc-code>
{
  pos := -1;
  var i := 1;
  while i < |arr|
    invariant 1 <= i <= |arr|
    invariant pos == -1 ==> forall j :: 1 <= j < i ==> arr[j] >= arr[j-1]
    invariant pos != -1 ==> 1 <= pos < i && arr[pos] < arr[pos-1]
    invariant pos != -1 ==> forall j :: pos < j < i ==> arr[j] >= arr[j-1]
  {
    if arr[i] < arr[i-1] {
      pos := i;
    }
    i := i + 1;
  }
}
// </vc-code>
