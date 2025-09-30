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
  index := 0;
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant 0 <= index < i
    invariant forall j :: 0 <= j < i ==> a[j] <= a[index]
    invariant forall j :: 0 <= j < i && a[j] == a[index] ==> index <= j
  {
    if a[i] > a[index] {
      index := i;
    }
    i := i + 1;
  }
}
// </vc-code>
