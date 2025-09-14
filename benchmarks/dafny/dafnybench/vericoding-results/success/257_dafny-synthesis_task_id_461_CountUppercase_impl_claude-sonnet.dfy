predicate IsUpperCase(c: char)
{
    65 <= c as int <= 90
}

// <vc-helpers>
lemma CountUppercaseHelper(s: string, i: int, currentCount: int, upperSet: set<int>)
    requires 0 <= i <= |s|
    requires upperSet == set j: int | 0 <= j < i && IsUpperCase(s[j])
    requires currentCount == |upperSet|
    ensures currentCount >= 0
    ensures currentCount == |set j: int | 0 <= j < i && IsUpperCase(s[j])|
{
}

lemma SetCardinalityIncrement(s: string, i: int)
    requires 0 <= i < |s|
    requires IsUpperCase(s[i])
    ensures |set j: int | 0 <= j < i+1 && IsUpperCase(s[j])| == |set j: int | 0 <= j < i && IsUpperCase(s[j])| + 1
{
    var oldSet := set j: int | 0 <= j < i && IsUpperCase(s[j]);
    var newSet := set j: int | 0 <= j < i+1 && IsUpperCase(s[j]);
    assert newSet == oldSet + {i};
    assert i !in oldSet;
}

lemma SetCardinalityNoChange(s: string, i: int)
    requires 0 <= i < |s|
    requires !IsUpperCase(s[i])
    ensures |set j: int | 0 <= j < i+1 && IsUpperCase(s[j])| == |set j: int | 0 <= j < i && IsUpperCase(s[j])|
{
    var oldSet := set j: int | 0 <= j < i && IsUpperCase(s[j]);
    var newSet := set j: int | 0 <= j < i+1 && IsUpperCase(s[j]);
    assert newSet == oldSet;
}
// </vc-helpers>

// <vc-spec>
method CountUppercase(s: string) returns (count: int)
    ensures count >= 0
    ensures count == | set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
// </vc-spec>
// <vc-code>
{
    count := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count >= 0
        invariant count == |set j: int | 0 <= j < i && IsUpperCase(s[j])|
    {
        if IsUpperCase(s[i]) {
            SetCardinalityIncrement(s, i);
            count := count + 1;
        } else {
            SetCardinalityNoChange(s, i);
        }
        i := i + 1;
    }
}
// </vc-code>

