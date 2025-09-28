// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added helper lemmas to prove postconditions */
predicate Contains(s: seq<int>, x: int)
{
  exists i :: 0 <= i < |s| && s[i] == x
}

predicate AllUnique(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

function RemoveDuplicates(s: seq<int>): seq<int>
  ensures AllUnique(RemoveDuplicates(s))
  ensures forall x :: Contains(s, x) <==> Contains(RemoveDuplicates(s), x)
  ensures forall i :: 0 <= i < |RemoveDuplicates(s)| ==> Contains(s, RemoveDuplicates(s)[i])
  decreases |s|
{
  if |s| == 0 then []
  else if Contains(s[1..], s[0]) then 
    RemoveDuplicatesLemma(s);
    RemoveDuplicates(s[1..])
  else 
    RemoveDuplicatesLemma(s);
    [s[0]] + RemoveDuplicates(s[1..])
}

lemma RemoveDuplicatesLemma(s: seq<int>)
  requires |s| > 0
  ensures Contains(s[1..], s[0]) ==> (forall x :: Contains(s, x) <==> Contains(RemoveDuplicates(s[1..]), x))
  ensures !Contains(s[1..], s[0]) ==> (forall x :: Contains(s, x) <==> (x == s[0] || Contains(RemoveDuplicates(s[1..]), x)))
{
  if Contains(s[1..], s[0]) {
    assert forall x :: Contains(s, x) <==> (x == s[0] || Contains(s[1..], x));
    assert forall x :: Contains(s[1..], s[0]) && x == s[0] ==> Contains(s[1..], x);
  } else {
    assert forall x :: Contains(s, x) <==> (x == s[0] || Contains(s[1..], x));
  }
}

lemma RemoveDuplicatesCorrect(s: seq<int>)
  ensures AllUnique(RemoveDuplicates(s))
  ensures forall x :: Contains(s, x) <==> Contains(RemoveDuplicates(s), x)
  ensures forall i :: 0 <= i < |RemoveDuplicates(s)| ==> Contains(s, RemoveDuplicates(s)[i])
{
}
// </vc-helpers>

// <vc-spec>
method SetToSeq(s: seq<int>) returns (result: seq<int>)
    ensures
        // All elements are unique in the result  
        forall i: int, j: int :: 0 <= i < j < |result| ==> result[i] != result[j]
    ensures
        // Every element in result is in s
        forall i: int :: 0 <= i < |result| ==> 
            exists j: int :: 0 <= j < |s| && s[j] == result[i]
    ensures
        // Every element in s is in result
        forall i: int :: 0 <= i < |s| ==> 
            exists j: int :: 0 <= j < |result| && result[j] == s[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added assertions to help verify postconditions */
{
  RemoveDuplicatesCorrect(s);
  result := RemoveDuplicates(s);
  assert AllUnique(result);
  assert forall x :: Contains(s, x) <==> Contains(result, x);
  assert forall i :: 0 <= i < |result| ==> Contains(s, result[i]);
  
  // Help Dafny prove the postconditions
  assert forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j] by {
    assert AllUnique(result);
  }
  
  assert forall i :: 0 <= i < |result| ==> exists j :: 0 <= j < |s| && s[j] == result[i] by {
    forall i | 0 <= i < |result| {
      assert Contains(s, result[i]);
    }
  }
  
  assert forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |result| && result[j] == s[i] by {
    forall i | 0 <= i < |s| {
      assert Contains(s, s[i]);
      assert Contains(result, s[i]);
    }
  }
}
// </vc-code>
