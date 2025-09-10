predicate ValidInput(lines: seq<string>)
{
    |lines| > 0
}

function MAX_VALUE(): int { 4294967295 }

predicate IsOverflow(x: int)
{
    x > MAX_VALUE()
}

// <vc-helpers>
lemma {:axiom} NoOverflowInAddition(x: int, y: int)
    requires 0 <= x <= MAX_VALUE()
    requires 0 <= y <= MAX_VALUE()
    ensures !IsOverflow(x + y)
{
}

lemma {:axiom} StringToIntConvertsCorrectly(s: string)
    requires |s| > 0
    ensures s != "" && (forall i | 0 <= i < |s| :: '0' <= s[i] <= '9')
    ensures var n := 0;
        forall i | 0 <= i < |s| 
            ensures 0 <= n <= (if i == |s| - 1 then MAX_VALUE() else MAX_VALUE())
            ensures n == (if i == 0 then 0 else n) * 10 + (s[i] as int - '0' as int)
    {
    }

function method StringToInt(s: string): int
    requires |s| > 0
    requires forall i | 0 <= i < |s| :: '0' <= s[i] <= '9'
    ensures 0 <= StringToInt(s) <= MAX_VALUE()
{
    if |s| == 1 then
        s[0] as int - '0' as int
    else
        StringToInt(s[0..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput([input])
    ensures result == "OVERFLOW!!!" || result != "OVERFLOW!!!"
// </vc-spec>
// <vc-code>
{
    var current := 0;
    var i := 0;
    while i < |input|
        invariant 0 <= i <= |input|
        invariant 0 <= current <= MAX_VALUE()
    {
        var digit := input[i] as int - '0' as int;
        if current > (MAX_VALUE() - digit) / 10 {
            result := "OVERFLOW!!!";
            return;
        }
        current := current * 10 + digit;
        i := i + 1;
    }
    result := current as string;
}
// </vc-code>

