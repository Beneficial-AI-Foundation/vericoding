// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Replaced selection sort with insertion sort to make postconditions verifiable */
method insertion_sort(s: seq<int>) returns (r: seq<int>)
  ensures |r| == |s|
  ensures multiset(s) == multiset(r)
  ensures forall i, j :: 0 <= i < j < |r| ==> r[i] <= r[j]
{
  r := [];
  var i := 0;
  while i < |s|
  {
    var item := s[i];
    var k := 0;
    while k < |r| && r[k] <= item
    {
      k := k + 1;
    }
    r := r[..k] + [item] + r[k..];
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method sorted_even(a: seq<int>) returns (sorted: seq<int>)

  requires |a| > 0

  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed to use insertion sort and ensure even positions are sorted as per postcondition */
  var evens := [];
  var i := 0;
  while i < |a|
  {
    if i % 2 == 0
    {
      evens := evens + [a[i]];
    }
    i := i + 1;
  }
  var sorted_evens := insertion_sort(evens);
  var result := [];
  var even_idx := 0;
  var j := 0;
  while j < |a|
  {
    if j % 2 == 0
    {
      result := result + [sorted_evens[even_idx]];
      even_idx := even_idx + 1;
    }
    else
    {
      result := result + [a[j]];
    }
    j := j + 1;
  }
  sorted := result;
}
// </vc-code>
