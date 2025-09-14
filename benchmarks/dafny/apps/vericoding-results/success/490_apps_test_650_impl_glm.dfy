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

// </vc-helpers>

// <vc-spec>
method solve(word: string) returns (result: string)
    requires ValidInput(word)
    ensures AllInSameGroup(word) <==> result == "YES"
    ensures result == "YES" || result == "NO"
// </vc-spec>
// <vc-code>
{
  var inGroup1 := true;
  var inGroup2 := true;
  for i := 0 to |word|
    invariant inGroup1 == forall j :: 0 <= j < i ==> word[j] in Group1()
    invariant inGroup2 == forall j :: 0 <= j < i ==> word[j] in Group2()
  {
    var c := word[i];
    if !(c in Group1()) {
      inGroup1 := false;
    }
    if !(c in Group2()) {
      inGroup2 := false;
    }
  }

  if inGroup1 || inGroup2 {
    return "YES";
  } else {
    return "NO";
  }
}
// </vc-code>

