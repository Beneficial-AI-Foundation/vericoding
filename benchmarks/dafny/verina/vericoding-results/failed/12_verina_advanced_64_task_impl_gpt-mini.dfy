// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial lemma placeholder to satisfy helper section */
lemma IdLemma5() ensures true {
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
  /* code modified by LLM (iteration 5): construct result by iterating and appending non-target elements */
  var res: seq<nat> := [];
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant forall k :: 0 <= k < |res| ==> res[k] != target
    invariant forall k :: 0 <= k < |res| ==> exists j :: 0 <= j < i && lst[j] == res[k] && lst[j] != target
    invariant forall a, b :: 0 <= a < b < i && lst[a] != target && lst[b] != target ==>
                (exists k1, k2 :: 0 <= k1 < k2 < |res| && res[k1] == lst[a] && res[k2] == lst[b])
    decreases |lst| - i
  {
    if lst[i] != target {
      res := res + [lst[i]];
    }
    i := i + 1;
  }
  result := res;
}

// </vc-code>
