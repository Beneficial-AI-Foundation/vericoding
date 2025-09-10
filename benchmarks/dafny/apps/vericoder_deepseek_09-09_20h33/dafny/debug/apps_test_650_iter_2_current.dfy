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
lemma AllInGroup1OrGroup2(word: string)
    requires ValidInput(word)
    ensures AllInGroup1(word) || AllInGroup2(word)
{
    var i := 0;
    while i < |word|
        invariant 0 <= i <= |word|
        invariant forall j :: 0 <= j < i ==> word[j] in Group1() || word[j] in Group2()
    {
        assert word[i] in Group1() || word[i] in Group2();
        i := i + 1;
    }
}

lemma NotAllInSameGroupImpliesMixed(word: string)
    requires ValidInput(word)
    ensures !AllInSameGroup(word) ==> (exists i, j :: 0 <= i < j < |word| && 
        ((word[i] in Group1() && word[j] in Group2()) || (word[i] in Group2() && word[j] in Group1())))
{
    if !AllInSameGroup(word) {
        var found1 := false;
        var found2 := false;
        var i := 0;
        var index1 := 0;
        var index2 := 0;
        
        while i < |word| 
            invariant 0 <= i <= |word|
            invariant found1 ==> exists j :: 0 <= j < i && word[j] in Group1()
            invariant found2 ==> exists j :: 0 <= j < i && word[j] in Group2()
        {
            if word[i] in Group1() {
                found1 := true;
                index1 := i;
            }
            if word[i] in Group2() {
                found2 := true;
                index2 := i;
            }
            i := i + 1;
        }
        
        if found1 && found2 {
            assert index1 < |word| && index2 < |word|;
            if index1 < index2 {
                assert word[index1] in Group1() && word[index2] in Group2();
            } else if index2 < index1 {
                assert word[index2] in Group2() && word[index1] in Group1();
            }
        }
    }
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
    if |word| == 1 {
        result := "YES";
    } else {
        var firstInGroup1 := word[0] in Group1();
        var allSame := true;
        var i := 1;
        
        while i < |word|
            invariant 1 <= i <= |word|
            invariant allSame ==> forall j :: 0 <= j < i ==> (word[j] in Group1()) == firstInGroup1
        {
            if (word[i] in Group1()) != firstInGroup1 {
                allSame := false;
            }
            i := i + 1;
        }
        
        if allSame {
            result := "YES";
        } else {
            result := "NO";
        }
    }
}
// </vc-code>

