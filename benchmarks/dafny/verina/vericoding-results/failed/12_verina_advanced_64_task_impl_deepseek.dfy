// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function countOccurrences(lst: seq<nat>, target: nat): nat
    decreases |lst|
{
    if |lst| == 0 then 0
    else (if lst[0] == target then 1 else 0) + countOccurrences(lst[1..], target)
}

/* helper modified by LLM (iteration 3): Remove problematic quantifier and use bounded approach */
function nonTargetElem(lst: seq<nat>, target: nat): set<nat>
{
    set x | x in lst && x != target
}

lemma countOccurrencesPreserved(lst1: seq<nat>, lst2: seq<nat>, target: nat, x: nat)
    requires x != target
    requires forall y :: y in lst1 ==> y != target
    requires forall y :: y in lst2 ==> y != target
    requires |lst1| == |lst2|
    requires multiset(lst1) == multiset(lst2)
    ensures countOccurrences(lst1, x) == countOccurrences(lst2, x)
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
  /* code modified by LLM (iteration 3): Use filter approach with bounded quantifier */
  result := [];
  var i := 0;
  
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant forall k :: 0 <= k < |result| ==> result[k] != target
    invariant forall k :: 0 <= k < |result| ==> k < i && lst[k] != target
    invariant |result| == countOccurrences(lst[0..i], target) == 0 ? i : |result|
  {
    if lst[i] != target {
      result := result + [lst[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
