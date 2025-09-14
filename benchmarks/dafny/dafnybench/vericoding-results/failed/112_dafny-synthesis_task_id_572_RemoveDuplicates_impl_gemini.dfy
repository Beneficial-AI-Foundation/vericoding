// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed syntax error in loop invariant */
  result := [];
  var seen: set<int> := {};
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
    invariant forall x :: x in result <==> x in seen
    invariant seen == set j | 0 <= j < i :: a[j]
  {
    var current_element := a[i];
    if current_element !in seen {
      result := result + [current_element];
      seen := seen + {current_element};
    } else {
      // The element is already in seen, do nothing to result, but we need to prove the invariant.
      // 'seen' is already equal to (set j | 0 <= j < i :: a[j]) + {a[i]}
      // because a[i] is already in the first part
    }
    i := i + 1;
  }
}
// </vc-code>
