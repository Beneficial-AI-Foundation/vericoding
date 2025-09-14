// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate InBoth(x: int, list1: seq<int>, list2: seq<int>)
{
  x in list1 && x in list2
}

predicate IsUnique(s: seq<int>, i: int)
  requires 0 <= i < |s|
{
  forall j :: 0 <= j < i ==> s[j] != s[i]
}

function CountShared(list1: seq<int>, list2: seq<int>, seen: seq<int>): nat
{
  if |list1| == 0 then 0
  else if list1[0] in list2 && list1[0] !in seen then
    1 + CountShared(list1[1..], list2, seen + [list1[0]])
  else
    CountShared(list1[1..], list2, seen)
}
// </vc-helpers>

// <vc-spec>
method SharedElements(list1: array<int>, list2: array<int>) returns (shared: array<int>)
    ensures
        forall i :: 0 <= i < shared.Length ==> (shared[i] in list1[..] && shared[i] in list2[..])
    ensures
        forall i, j :: 0 <= i < j < shared.Length ==> shared[i] != shared[j]
// </vc-spec>
// <vc-code>
{
  var result := [];
  var i := 0;
  
  while i < list1.Length
    invariant 0 <= i <= list1.Length
    invariant forall k :: 0 <= k < |result| ==> result[k] in list1[..] && result[k] in list2[..]
    invariant forall k, j :: 0 <= k < j < |result| ==> result[k] != result[j]
  {
    if list1[i] in list2[..] {
      var alreadyAdded := false;
      var j := 0;
      while j < |result|
        invariant 0 <= j <= |result|
        invariant alreadyAdded <==> exists k :: 0 <= k < j && result[k] == list1[i]
      {
        if result[j] == list1[i] {
          alreadyAdded := true;
        }
        j := j + 1;
      }
      
      if !alreadyAdded {
        result := result + [list1[i]];
      }
    }
    i := i + 1;
  }
  
  shared := new int[|result|];
  i := 0;
  while i < |result|
    invariant 0 <= i <= |result|
    invariant forall k :: 0 <= k < i ==> shared[k] == result[k]
  {
    shared[i] := result[i];
    i := i + 1;
  }
}
// </vc-code>
