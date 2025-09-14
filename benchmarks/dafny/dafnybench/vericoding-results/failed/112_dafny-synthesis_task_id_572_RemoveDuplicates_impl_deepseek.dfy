

// <vc-helpers>
predicate isUnique(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

lemma UniqueAdd(s: seq<int>, x: int)
  requires isUnique(s) && (forall i :: 0 <= i < |s| ==> s[i] != x)
  ensures isUnique(s + [x])
{
}

lemma SetSeqCorrespondence(s: seq<int>)
  ensures set x | x in s == set x | x in s
{
}

lemma SeenContainsResult(result: seq<int>, seen: set<int>)
  ensures set x | x in result <= seen
{
}

lemma UniqueFromSet(result: seq<int>, seen: set<int>)
  requires forall x :: x in result <==> x in seen
  requires |result| == |seen|
  ensures isUnique(result)
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  result := [];
  var seen: set<int> := {};
  
  var i: int := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: x in result <==> x in seen
    invariant isUnique(result)
    invariant seen == set x | x in result
    invariant forall x :: x in seen <==> exists j :: 0 <= j < i && a[j] == x
  {
    if a[i] !in seen {
      seen := seen + {a[i]};
      result := result + [a[i]];
    }
    i := i + 1;
  }
}
// </vc-code>

