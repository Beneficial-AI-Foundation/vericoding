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
lemma CharInExactlyOneGroup(c: char)
    requires 'A' <= c <= 'Z'
    ensures (c in Group1()) != (c in Group2())
{
    assert c in Group1() || c in Group2();
    assert !(c in Group1() && c in Group2());
}

lemma NotAllInGroup1ImpliesExistsNotInGroup1(word: string)
    requires ValidInput(word)
    requires !AllInGroup1(word)
    ensures exists i :: 0 <= i < |word| && word[i] !in Group1()
{
}

lemma NotAllInGroup2ImpliesExistsNotInGroup2(word: string)
    requires ValidInput(word)
    requires !AllInGroup2(word)
    ensures exists i :: 0 <= i < |word| && word[i] !in Group2()
{
}
// </vc-helpers>

// <vc-spec>
method solve(word: string) returns (result: string)
    requires ValidInput(word)
    ensures AllInSameGroup(word) <==> result == "YES"
    ensures result == "YES" || result == "NO"
// </vc-spec>
// <vc-code>
{
    var allGroup1 := true;
    var allGroup2 := true;
    
    var i := 0;
    while i < |word|
        invariant 0 <= i <= |word|
        invariant allGroup1 ==> forall j :: 0 <= j < i ==> word[j] in Group1()
        invariant allGroup2 ==> forall j :: 0 <= j < i ==> word[j] in Group2()
        invariant !allGroup1 ==> exists j :: 0 <= j < i && word[j] !in Group1()
        invariant !allGroup2 ==> exists j :: 0 <= j < i && word[j] !in Group2()
    {
        if word[i] !in Group1() {
            allGroup1 := false;
        }
        if word[i] !in Group2() {
            allGroup2 := false;
        }
        i := i + 1;
    }
    
    if allGroup1 || allGroup2 {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

