predicate ValidInput(s: string) {
    |s| == 4 && forall i :: 0 <= i < |s| ==> s[i] == '+' || s[i] == '-'
}

function CountChar(s: string, c: char): int
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

function CalculateSum(s: string): int
    requires ValidInput(s)
{
    CountChar(s, '+') - CountChar(s, '-')
}

// <vc-helpers>
lemma CountCharSlice(s: string, c: char, start: nat)
    requires start <= |s|
    ensures CountChar(s, c) == CountChar(s[..start], c) + CountChar(s[start..], c)
    decreases |s| - start
{
    if start == |s| {
        // Base case: empty slice
    } else {
        CountCharSlice(s, c, start + 1);
        // Recursive call to prove the property
    }
}

lemma CountCharEmpty(c: char)
    ensures CountChar("", c) == 0
{
    // Trivial: empty string has count 0
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result == CalculateSum(s)
// </vc-spec>
// <vc-code>
{
    var count := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == CountChar(s[..i], '+') - CountChar(s[..i], '-')
        decreases |s| - i
    {
        if s[i] == '+' {
            count := count + 1;
        } else if s[i] == '-' {
            count := count - 1;
        }
        i := i + 1;
    }
    result := count;
}
// </vc-code>

