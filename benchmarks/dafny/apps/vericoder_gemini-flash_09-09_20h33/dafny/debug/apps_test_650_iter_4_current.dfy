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
function IsInGroup1Char(c: char): bool {
  c in Group1()
}

function IsInGroup2Char(c: char): bool {
  c in Group2()
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
    var group1Count := 0;
    var group2Count := 0;

    for i := 0 to |word| - 1
        invariant 0 <= i <= |word|
        invariant 0 <= group1Count <= i
        invariant 0 <= group2Count <= i
        invariant group1Count == (count l :: 0 <= l < i && IsInGroup1Char(word[l]))
        invariant group2Count == (count l :: 0 <= l < i && IsInGroup2Char(word[l]))
    {
        if IsInGroup1Char(word[i]) {
            group1Count := group1Count + 1;
        } else if IsInGroup2Char(word[i]) {
            group2Count := group2Count + 1;
        }
    }

    if (group1Count == |word| || group2Count == |word|) {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

