// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clauses and improved helper functions */
function Sort(s: seq<int>): seq<int>
  decreases |s|
  ensures |Sort(s)| == |s|
  ensures forall i, j :: 0 <= i < j < |Sort(s)| ==> Sort(s)[i] <= Sort(s)[j]
  ensures multiset(s) == multiset(Sort(s))
{
  if |s| <= 1 then
    s
  else
    var left := FilterLessOrEqual(s[1..], s[0]);
    var right := FilterGreater(s[1..], s[0]);
    Sort(left) + [s[0]] + Sort(right)
}

function FilterLessOrEqual(s: seq<int>, pivot: int): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else if s[0] <= pivot then [s[0]] + FilterLessOrEqual(s[1..], pivot)
  else FilterLessOrEqual(s[1..], pivot)
}

function FilterGreater(s: seq<int>, pivot: int): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else if s[0] > pivot then [s[0]] + FilterGreater(s[1..], pivot)
  else FilterGreater(s[1..], pivot)
}

predicate Sorted(a: seq<int>) { forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j] }
lemma SortPreservesMultiset(s: seq<int>)
  ensures multiset(Sort(s)) == multiset(s)
{
}
// </vc-helpers>

// <vc-spec>
method UniqueSorted(arr: array<int>) returns (result: array<int>)
    ensures result.Length <= arr.Length
    ensures forall i :: 0 <= i < result.Length - 1 ==> result[i] <= result[i + 1]
    ensures forall x :: x in arr[..] <==> x in result[..]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed loop invariant and ensured array bounds */
{
  if arr.Length == 0 {
    result := new int[0];
    return;
  }
  
  var sorted_seq := Sort(arr[..]);
  
  var unique: seq<int> := [];
  var index := 0;
  
  while index < |sorted_seq|
    decreases |sorted_seq| - index
    invariant 0 <= index <= |sorted_seq|
    invariant |unique| <= index
    invariant forall x :: x in unique <==> x in sorted_seq[0..index]
    invariant Sorted(unique)
    invariant forall i :: 0 <= i < |unique| - 1 ==> unique[i] <= unique[i + 1]
  {
    if index == 0 || sorted_seq[index] != sorted_seq[index - 1] {
      unique := unique + [sorted_seq[index]];
    }
    index := index + 1;
  }
  
  result := new int[|unique|];
  if |unique| > 0 {
    for i := 0 to |unique| - 1
      invariant result.Length == |unique|
      invariant forall j :: 0 <= j < i ==> result[j] == unique[j]
    {
      result[i] := unique[i];
    }
  }
}
// </vc-code>
