// <vc-preamble>
// Helper predicate to count True values in a boolean sequence
function CountTrue(condition: seq<bool>): nat
{
    if |condition| == 0 then 0
    else (if condition[0] then 1 else 0) + CountTrue(condition[1..])
}

// Helper predicate to check if result contains elements from arr where condition is True, in order
ghost predicate ValidExtract(condition: seq<bool>, arr: seq<real>, result: seq<real>)
  requires |condition| == |arr|
{
    |result| == CountTrue(condition) &&
    exists mapping: seq<nat> ::
      |mapping| == |result| &&
      (forall i :: 0 <= i < |mapping| ==> 
        0 <= mapping[i] < |condition| &&
        condition[mapping[i]]) &&
      (forall i :: 0 <= i < |result| ==> 
        result[i] == arr[mapping[i]]) &&
      (forall i, j :: 0 <= i < j < |mapping| ==> 
        mapping[i] < mapping[j])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed lemma proof by handling sequence slicing correctly */
lemma CountTrueSlice(condition: seq<bool>, i: nat)
  requires i < |condition|
  ensures CountTrue(condition[..i+1]) == CountTrue(condition[..i]) + (if condition[i] then 1 else 0)
{
  if i == 0 {
    assert condition[..1] == [condition[0]];
    assert CountTrue(condition[..0]) == 0;
  } else {
    var prefix := condition[..i];
    var extended := condition[..i+1];
    assert extended == prefix + [condition[i]];
    CountTrueAppend(prefix, [condition[i]]);
  }
}

/* helper modified by LLM (iteration 4): Added lemma for CountTrue append property */
lemma CountTrueAppend(s1: seq<bool>, s2: seq<bool>)
  ensures CountTrue(s1 + s2) == CountTrue(s1) + CountTrue(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    assert (s1 + s2)[0] == s1[0];
    assert (s1 + s2)[1..] == s1[1..] + s2;
    CountTrueAppend(s1[1..], s2);
  }
}

/* helper modified by LLM (iteration 4): Added lemma to connect condition prefix with full condition */
lemma CountTrueComplete(condition: seq<bool>)
  ensures CountTrue(condition[..|condition|]) == CountTrue(condition)
{
  assert condition[..|condition|] == condition;
}
// </vc-helpers>

// <vc-spec>
method Extract(condition: seq<bool>, arr: seq<real>) returns (result: seq<real>)
  requires |condition| == |arr|
  ensures ValidExtract(condition, arr, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Added final lemma call to establish connection */
  result := [];
  var mapping := [];
  
  for i := 0 to |condition|
    invariant |result| == |mapping|
    invariant |result| == CountTrue(condition[..i])
    invariant forall j :: 0 <= j < |mapping| ==> 0 <= mapping[j] < i && condition[mapping[j]]
    invariant forall j :: 0 <= j < |result| ==> result[j] == arr[mapping[j]]
    invariant forall j, k :: 0 <= j < k < |mapping| ==> mapping[j] < mapping[k]
  {
    CountTrueSlice(condition, i);
    if condition[i] {
      result := result + [arr[i]];
      mapping := mapping + [i];
    }
  }
  
  CountTrueComplete(condition);
  
  // Help Dafny see that mapping is the witness for ValidExtract
  assert |mapping| == |result|;
  assert |result| == CountTrue(condition);
  assert forall j :: 0 <= j < |mapping| ==> 0 <= mapping[j] < |condition| && condition[mapping[j]];
  assert forall j :: 0 <= j < |result| ==> result[j] == arr[mapping[j]];
  assert forall j, k :: 0 <= j < k < |mapping| ==> mapping[j] < mapping[k];
}
// </vc-code>
