// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed index bounds checking for sequences */
predicate HasConsecutiveAt(a: seq<int>, i: int) 
  requires 0 <= i < |a| - 1
{
  a[i] + 1 == a[i + 1]
}
// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(a: seq<int>) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |a| - 1 && a[i] + 1 == a[i + 1]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed index access bounds in loop invariant */
{
  var index := 0;
  result := false;
  
  while index < |a| - 1
    invariant 0 <= index <= |a|
    invariant !result ==> !(exists j :: 0 <= j < index && j + 1 < |a| && a[j] + 1 == a[j + 1])
    invariant result ==> (exists j :: 0 <= j < |a| - 1 && a[j] + 1 == a[j + 1])
    decreases |a| - index
  {
    if a[index] + 1 == a[index + 1] {
      result := true;
      return;
    }
    index := index + 1;
  }
}
// </vc-code>
