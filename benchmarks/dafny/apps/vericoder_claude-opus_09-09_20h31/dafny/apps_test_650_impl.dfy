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
lemma Group1Group2Disjoint()
    ensures forall c :: c in Group1() ==> c !in Group2()
    ensures forall c :: c in Group2() ==> c !in Group1()
{
    // The groups are disjoint by definition
}

lemma CheckAllInGroup1(word: string, k: nat)
    requires 0 <= k <= |word|
    requires forall i :: 0 <= i < k ==> word[i] in Group1()
    ensures forall i :: 0 <= i < k ==> word[i] in Group1()
{
    // This lemma maintains the loop invariant
}

lemma CheckAllInGroup2(word: string, k: nat)
    requires 0 <= k <= |word|
    requires forall i :: 0 <= i < k ==> word[i] in Group2()
    ensures forall i :: 0 <= i < k ==> word[i] in Group2()
{
    // This lemma maintains the loop invariant
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
    var inGroup1 := true;
    var inGroup2 := true;
    var i := 0;
    
    while i < |word|
        invariant 0 <= i <= |word|
        invariant inGroup1 ==> forall j :: 0 <= j < i ==> word[j] in Group1()
        invariant !inGroup1 ==> exists j :: 0 <= j < i && word[j] !in Group1()
        invariant inGroup2 ==> forall j :: 0 <= j < i ==> word[j] in Group2()
        invariant !inGroup2 ==> exists j :: 0 <= j < i && word[j] !in Group2()
    {
        if inGroup1 && word[i] !in Group1() {
            inGroup1 := false;
        }
        if inGroup2 && word[i] !in Group2() {
            inGroup2 := false;
        }
        i := i + 1;
    }
    
    if inGroup1 || inGroup2 {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

