// <vc-preamble>
// Returns the index of the maximum element in a non-empty sequence of real numbers
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): placeholder helper (no-op) */
lemma ArgmaxHelpers() {
}

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
  /* code modified by LLM (iteration 2): maintain strictness invariant to ensure first occurrence */
  var n := |a|;
  var i := 1;
  index := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= index < n
    invariant forall j :: 0 <= j < i ==> a[j] <= a[index]
    invariant forall k :: 0 <= k < index ==> a[k] < a[index]
    decreases n - i
  {
    if a[index] < a[i] {
      index := i;
    }
    i := i + 1;
  }
}

// </vc-code>
