predicate ValidInput(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] == 'x' || s[i] == 'y'
}

function countChar(s: string, c: char): nat
{
    |set i | 0 <= i < |s| && s[i] == c|
}

predicate ValidOutput(s: string, result: string)
    requires ValidInput(s)
{
    var countX := countChar(s, 'x');
    var countY := countChar(s, 'y');
    if countY > countX then
        |result| == countY - countX && forall i :: 0 <= i < |result| ==> result[i] == 'y'
    else
        |result| == countX - countY && forall i :: 0 <= i < |result| ==> result[i] == 'x'
}

// <vc-helpers>
lemma CountCharCorrect(s: string, c: char, count: nat)
    requires forall i :: 0 <= i < |s| ==> s[i] == 'x' || s[i] == 'y'
    requires count == |set i | 0 <= i < |s| && s[i] == c|
    ensures count == countChar(s, c)
{
}

lemma SetCardinalityIncrease(s: string, i: nat, c: char)
    requires ValidInput(s)
    requires 0 <= i < |s|
    requires s[i] == c
    ensures |set j | 0 <= j < i+1 && s[j] == c| == |set j | 0 <= j < i && s[j] == c| + 1
{
    var S1 := set j | 0 <= j < i && s[j] == c;
    var S2 := set j | 0 <= j < i+1 && s[j] == c;
    assert S2 == S1 + {i};
    assert i !in S1;
}

lemma SetCardinalitySame(s: string, i: nat, c: char, d: char)
    requires ValidInput(s)
    requires 0 <= i < |s|
    requires s[i] == d && d != c
    ensures |set j | 0 <= j < i+1 && s[j] == c| == |set j | 0 <= j < i && s[j] == c|
{
    var S1 := set j | 0 <= j < i && s[j] == c;
    var S2 := set j | 0 <= j < i+1 && s[j] == c;
    assert S2 == S1;
}

method CountChars(s: string) returns (xCount: nat, yCount: nat)
    requires ValidInput(s)
    ensures xCount == countChar(s, 'x')
    ensures yCount == countChar(s, 'y')
{
    xCount := 0;
    yCount := 0;
    
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant xCount == |set j | 0 <= j < i && s[j] == 'x'|
        invariant yCount == |set j | 0 <= j < i && s[j] == 'y'|
    {
        if s[i] == 'x' {
            SetCardinalityIncrease(s, i, 'x');
            SetCardinalitySame(s, i, 'y', 'x');
            xCount := xCount + 1;
        } else {
            SetCardinalityIncrease(s, i, 'y');
            SetCardinalitySame(s, i, 'x', 'y');
            yCount := yCount + 1;
        }
    }
    
    CountCharCorrect(s, 'x', xCount);
    CountCharCorrect(s, 'y', yCount);
}

method CreateString(c: char, n: nat) returns (result: string)
    ensures |result| == n
    ensures forall i :: 0 <= i < |result| ==> result[i] == c
{
    result := "";
    for i := 0 to n
        invariant 0 <= i <= n
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == c
    {
        result := result + [c];
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
    var xCount, yCount := CountChars(s);
    
    if yCount > xCount {
        result := CreateString('y', yCount - xCount);
    } else {
        result := CreateString('x', xCount - yCount);
    }
}
// </vc-code>

