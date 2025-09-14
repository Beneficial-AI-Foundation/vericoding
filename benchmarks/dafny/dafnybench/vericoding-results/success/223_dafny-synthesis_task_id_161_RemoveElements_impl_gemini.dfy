// <vc-preamble>
predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RemoveElements(a: array<int>, b: array<int>) returns (result: seq<int>)

    ensures forall x :: x in result ==> InArray(a, x) && !InArray(b, x)

    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed compilation error in set comprehension syntax */
  var b_set: set<int> := {};
  var j := 0;
  while j < b.Length
    invariant 0 <= j <= b.Length
    invariant b_set == (set k | 0 <= k < j :: b[k])
  {
    b_set := b_set + {b[j]};
    j := j + 1;
  }

  result := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: x in result ==> (exists k :: 0 <= k < i && a[k] == x)
    invariant forall x :: x in result ==> x !in b_set
    invariant forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
  {
    var x := a[i];
    if x !in b_set && x !in result {
      result := result + [x];
    }
    i := i + 1;
  }
}
// </vc-code>
