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
function FindStartPosition(s: string, pos: int): int
    requires 0 <= pos <= |s|
    decreases |s| - pos
    ensures 0 <= return <= |s|
{
    if pos >= |s| then pos
    else if '0' <= s[pos] <= '9' then pos
    else FindStartPosition(s, pos+1)
}

function ParseIntegerFromPosition(s: string, pos: int, acc: int): int
    requires 0 <= pos <= |s|
    decreases |s| - pos
{
    if pos >= |s| then acc
    else if '0' <= s[pos] <= '9' then ParseIntegerFromPosition(s, pos+1, acc * 10 + (s[pos] as int - '0' as int))
    else acc
}

function ParseIntegerHelper(s: string, pos: int): int
    requires 0 <= pos <= |s|
    decreases |s| - pos
{
    ParseIntegerFromPosition(s, FindStartPosition(s, pos), 0)
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
    result := if IsCelebratedAge(n) then "YES\n" else "NO\n";
}
// </vc-code>

