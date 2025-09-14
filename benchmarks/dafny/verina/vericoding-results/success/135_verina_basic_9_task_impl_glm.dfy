// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires 
        a.Length > 0 &&
        b.Length > 0
    ensures
        result == (exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Moved implementation from helpers section to code section */
  var i := 0;
  while i < a.Length
      invariant 0 <= i <= a.Length
      invariant forall j :: 0 <= j < i ==> forall k :: 0 <= k < b.Length ==> a[j] != b[k]
  {
      var j := 0;
      while j < b.Length
          invariant 0 <= j <= b.Length
          invariant forall k :: 0 <= k < j ==> a[i] != b[k]
      {
          if a[i] == b[j] {
              return true;
          }
          j := j + 1;
      }
      i := i + 1;
  }
  return false;
}
// </vc-code>
