// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive FilterPrefix builds seq of non-target from prefix */
function FilterPrefix(lst: seq<nat>, idx: int, target: nat): seq<nat>
  requires 0 <= idx <= |lst|
  decreases idx
{
  if idx == 0 then [] else if lst[idx-1] != target then FilterPrefix(lst, idx-1, target) + [lst[idx-1]] else FilterPrefix(lst, idx-1, target)
}

/* helper modified by LLM (iteration 5): predicate for non-target */
predicate IsNotTarget(x: nat, t: nat) { x != t }
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
  /* code modified by LLM (iteration 5): build filtered sequence using helper FilterPrefix */
  result := FilterPrefix(lst, |lst|, target);
}
// </vc-code>
