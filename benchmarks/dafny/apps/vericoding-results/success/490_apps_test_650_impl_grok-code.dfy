predicate ValidInput(word: string) 
{
    1 <= |word| <= 10 && forall i :: 0 <= i < |word| ==> 'A' <= word[i] <= 'Z'
}

function Group1(): string { "AEFHIKLMNTVWXYZ" }
function Group2(): string { "BCDGJOPQRSU" }

predicate AllInGroup1(word: string)
{
    forall i :: 0 <= i < |word| ==> word[i] in Group1()
}

predicate AllInGroup2(word: string)
{
    forall i :: 0 <= i < |word| ==> word[i] in Group2()
}

predicate AllInSameGroup(word: string)
{
    AllInGroup1(word) || AllInGroup2(word)
}

// <vc-helpers>
// Helpers remain empty as existing predicates and functions suffice for verification
// </vc-helpers>

// <vc-spec>
method solve(word: string) returns (result: string)
    requires ValidInput(word)
    ensures AllInSameGroup(word) <==> result == "YES"
    ensures result == "YES" || result == "NO"
// </vc-spec>
// <vc-code>
{
  var g1 := Group1();
  var g2 := Group2();
  var inG1 := true;
  var inG2 := true;
  var i := 0;
  while i < |word|
    invariant 0 <= i <= |word|
    invariant inG1 == forall k :: 0 <= k < i ==> word[k] in g1
    invariant inG2 == forall k :: 0 <= k < i ==> word[k] in g2
  {
    if word[i] !in g1 {
      inG1 := false;
    }
    if word[i] !in g2 {
      inG2 := false;
    }
    i := i + 1;
  }
  result := if inG1 || inG2 then "YES" else "NO";
}
// </vc-code>

