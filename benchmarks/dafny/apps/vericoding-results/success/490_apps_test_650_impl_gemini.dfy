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
  var all_in_g1 := true;
  var all_in_g2 := true;
  var i := 0;
  while i < |word|
    invariant 0 <= i <= |word|
    invariant all_in_g1 == forall k :: 0 <= k < i ==> word[k] in Group1()
    invariant all_in_g2 == forall k :: 0 <= k < i ==> word[k] in Group2()
  {
    var c := word[i];
    if c !in Group1() {
      all_in_g1 := false;
    }
    if c !in Group2() {
      all_in_g2 := false;
    }
    i := i + 1;
  }

  if all_in_g1 || all_in_g2 {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

