predicate ValidInput(s: string)
{
    |s| > 0 && exists i: int :: 0 <= i < |s| && '0' <= s[i] <= '9'
}

predicate IsCelebratedAge(age: int)
{
    age == 3 || age == 5 || age == 7
}

function ParseIntegerValue(s: string): int
    requires |s| > 0
    requires exists i: int :: 0 <= i < |s| && '0' <= s[i] <= '9'
{
    ParseIntegerHelper(s, 0)
}

// <vc-helpers>
function ParseIntegerHelper(s: string, acc: int): int
    decreases |s|
    requires |s| > 0
    requires exists i: int :: 0 <= i < |s| && '0' <= s[i] <= '9'
    ensures ParseIntegerHelper(s, acc) >= 0
{
    if |s| == 1 then
        if '0' <= s[0] <= '9' then
            acc * 10 + (s[0] as int - '0' as int)
        else
            acc
    else if '0' <= s[0] <= '9' then
        ParseIntegerHelper(s[1..], acc * 10 + (s[0] as int - '0' as int))
    else
        ParseIntegerHelper(s[1..], acc)
}

lemma ParseIntegerHelperValid(s: string, acc: int)
    requires |s| > 0
    requires exists i: int :: 0 <= i < |s| && '0' <= s[i] <= '9'
    ensures var parsed := ParseIntegerHelper(s, acc);
            parsed >= 0
    decreases |s|
{
    if |s| == 1 {
        // Base case: single character string
    } else if '0' <= s[0] <= '9' {
        assert |s[1..]| > 0;
        assert (exists i: int :: 0 <= i < |s[1..]| && '0' <= s[1..][i] <= '9') || (|s[1..]| == 0);
        ParseIntegerHelperValid(s[1..], acc * 10 + (s[0] as int - '0' as int));
    } else {
        assert |s[1..]| > 0;
        assert (exists i: int :: 0 <= i < |s[1..]| && '0' <= s[1..][i] <= '9') || (|s[1..]| == 0);
        ParseIntegerHelperValid(s[1..], acc);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures var n := ParseIntegerValue(stdin_input); 
            IsCelebratedAge(n) ==> result == "YES\n"
    ensures var n := ParseIntegerValue(stdin_input);
            !IsCelebratedAge(n) ==> result == "NO\n"
    ensures result == "YES\n" || result == "NO\n"
// </vc-spec>
// <vc-code>
{
    var n := ParseIntegerValue(stdin_input);
    if n == 3 || n == 5 || n == 7 {
        result := "YES\n";
    } else {
        result := "NO\n";
    }
}
// </vc-code>

