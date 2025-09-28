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
// no helper updates needed
// </vc-helpers>

// <vc-spec>
method solve(word: string) returns (result: string)
    requires ValidInput(word)
    ensures AllInSameGroup(word) <==> result == "YES"
    ensures result == "YES" || result == "NO"
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var allG1 := true;
  var allG2 := true;
  while i < |word|
    invariant 0 <= i <= |word|
    invariant allG1 == (forall j :: 0 <= j < i ==> word[j] in Group1())
    invariant allG2 == (forall j :: 0 <= j < i ==> word[j] in Group2())
    decreases |word| - i
  {
    var c := word[i];
    allG1 := allG1 && c in Group1();
    allG2 := allG2 && c in Group2();
    i := i + 1;
  }
  assert i == |word|;
  assert allG1 == (forall j :: 0 <= j < |word| ==> word[j] in Group1());
  assert allG2 == (forall j :: 0 <= j < |word| ==> word[j] in Group2());
  assert AllInGroup1(word) == (forall j :: 0 <= j < |word| ==> word[j] in Group1());
  assert AllInGroup2(word) == (forall j :: 0 <= j < |word| ==> word[j] in Group2());
  var inSame := allG1 || allG2;
  assert inSame <==> AllInSameGroup(word);
  if inSame {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

