// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed function syntax and sequence comprehensions */
function ToSet(s: seq<int>): set<int>
{
  set i | 0 <= i < |s| :: s[i]
}

function RemoveDuplicates(s: seq<int>): seq<int>
  ensures forall x :: x in s <==> x in RemoveDuplicates(s)
  ensures forall i, j :: 0 <= i < j < |RemoveDuplicates(s)| ==> RemoveDuplicates(s)[i] != RemoveDuplicates(s)[j]
{
  if |s| == 0 then []
  else if s[0] in RemoveDuplicates(s[1..]) then RemoveDuplicates(s[1..])
  else [s[0]] + RemoveDuplicates(s[1..])
}

function Sort(s: seq<int>): seq<int>
  ensures |Sort(s)| == |s|
  ensures multiset(s) == multiset(Sort(s))
  ensures forall i, j :: 0 <= i < j < |Sort(s)| ==> Sort(s)[i] <= Sort(s)[j]
  decreases |s|
{
  if |s| <= 1 then s
  else
    var pivot := s[0];
    var rest := s[1..];
    var less := if |rest| == 0 then [] else seq(|rest|, i requires 0 <= i < |rest| => if rest[i] < pivot then rest[i] else pivot)[..i | 0 <= i < |rest| && rest[i] < pivot];
    var equal := [pivot];
    var greater := if |rest| == 0 then [] else seq(|rest|, i requires 0 <= i < |rest| => if rest[i] > pivot then rest[i] else pivot)[..i | 0 <= i < |rest| && rest[i] > pivot];
    Sort(less) + equal + Sort(greater)
}

function FilterOut(s: seq<int>, toRemove: set<int>): seq<int>
  ensures forall x :: x in FilterOut(s, toRemove) ==> x in s && x !in toRemove
  ensures forall x :: x in s && x !in toRemove ==> x in FilterOut(s, toRemove)
{
  if |s| == 0 then []
  else if s[0] in toRemove then FilterOut(s[1..], toRemove)
  else [s[0]] + FilterOut(s[1..], toRemove)
}
// </vc-helpers>

// <vc-spec>
method setdiff1d(ar1: seq<int>, ar2: seq<int>) returns (result: seq<int>)
    // Each element in result is from ar1 and not in ar2
    ensures forall i :: 0 <= i < |result| ==> 
        (exists j :: 0 <= j < |ar1| && result[i] == ar1[j]) &&
        (forall k :: 0 <= k < |ar2| ==> result[i] != ar2[k])
    
    // No duplicates in result
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    
    // Result is sorted in ascending order
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
    
    // All unique values from ar1 not in ar2 are included in result
    ensures forall val {:trigger val in ar1} :: 
        ((exists i :: 0 <= i < |ar1| && ar1[i] == val) && 
         (forall j :: 0 <= j < |ar2| ==> ar2[j] != val)) ==>
        (exists k :: 0 <= k < |result| && result[k] == val)
    
    // Completeness: result contains exactly the values that should be there
    ensures forall val :: 
        (val in result) <==> 
        (val in ar1 && val !in ar2)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Keep same implementation */
  var ar2Set := ToSet(ar2);
  var filtered := FilterOut(ar1, ar2Set);
  var unique := RemoveDuplicates(filtered);
  result := Sort(unique);
}
// </vc-code>
