// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function CountOccurrences(lst: seq<nat>, target: nat): nat
  ensures CountOccurrences(lst, target) == |lst| - |lst[|lst| - CountOccurrences(lst, target)..]|
{
  if |lst| == 0 then 0
  else (if lst[0] == target then 1 else 0) + CountOccurrences(lst[1..], target)
}

lemma RemoveElementPreservesOrder(lst: seq<nat>, target: nat, result: seq<nat>)
  requires forall i :: 0 <= i < |result| ==> result[i] != target
  requires forall i :: 0 <= i < |result| ==> 
            exists j :: 0 <= j < |lst| && lst[j] == result[i] && lst[j] != target
  ensures forall i, j :: 0 <= i < j < |lst| && lst[i] != target && lst[j] != target ==> 
            (exists k1, k2 :: 0 <= k1 < k2 < |result| && 
            result[k1] == lst[i] && result[k2] == lst[j])
{
}
// </vc-helpers>

// <vc-spec>
method RemoveElement(lst: seq<nat>, target: nat) returns (result: seq<nat>)
    ensures
        forall i :: 0 <= i < |result| ==> result[i] != target
    ensures
        forall i :: 0 <= i < |result| ==> 
            exists j :: 0 <= j < |lst| && lst[j] == result[i] && lst[j] != target
    ensures
        forall i, j :: 0 <= i < j < |lst| && lst[i] != target && lst[j] != target ==> 
            (exists k1, k2 :: 0 <= k1 < k2 < |result| && 
            result[k1] == lst[i] && result[k2] == lst[j])
// </vc-spec>
// <vc-code>
{
  var index := 0;
  result := [];
  
  while index < |lst|
    invariant forall k :: 0 <= k < |result| ==> result[k] != target
    invariant forall k :: 0 <= k < |result| ==> 
              exists j :: 0 <= j < index && lst[j] == result[k] && lst[j] != target
    invariant forall i, j :: 0 <= i < j < index && lst[i] != target && lst[j] != target ==> 
              (exists k1, k2 :: 0 <= k1 < k2 < |result| && 
              result[k1] == lst[i] && result[k2] == lst[j])
  {
    if lst[index] != target {
      result := result + [lst[index]];
    }
    index := index + 1;
  }
}
// </vc-code>
