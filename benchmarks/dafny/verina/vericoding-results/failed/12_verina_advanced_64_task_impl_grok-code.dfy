// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Filtered(lst: seq<nat>, limit: int, target: nat): seq<nat>
requires 0 <= limit <= |lst|
decreases limit
{
  if limit == 0 then []
  else if lst[limit-1] != target then Filtered(lst, limit-1, target) + [lst[limit-1]]
  else Filtered(lst, limit-1, target)
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
  /* code modified by LLM (iteration 5): used helper function for recursive filtering to fix syntax and ensure order preservation */
  result := Filtered(lst, |lst|, target);
}
// </vc-code>
