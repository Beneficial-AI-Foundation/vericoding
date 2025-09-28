// <vc-preamble>
// Returns the index of the maximum element in a non-empty sequence of real numbers
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method argmax(a: seq<real>) returns (index: nat)
  // Precondition: sequence must be non-empty
  requires |a| > 0
  // Postcondition: returned index is valid for the sequence
  ensures 0 <= index < |a|
  // Postcondition: element at returned index is maximum (greater than or equal to all other elements)
  ensures forall j :: 0 <= j < |a| ==> a[j] <= a[index]
  // Postcondition: returned index is the first occurrence of the maximum value
  ensures forall j :: 0 <= j < |a| && a[j] == a[index] ==> index <= j
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added invariant i <= |a| to fix index bounds and postcondition */
  var maxIndex := 0;
  var i := 1;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant 0 <= maxIndex < i
    invariant forall j :: 0 <= j < i ==> a[j] <= a[maxIndex]
    invariant forall j :: 0 <= j < i && a[j] == a[maxIndex] ==> maxIndex <= j
  {
    if a[i] > a[maxIndex] {
      maxIndex := i;
    }
    i := i + 1;
  }
  index := maxIndex;
}
// </vc-code>
