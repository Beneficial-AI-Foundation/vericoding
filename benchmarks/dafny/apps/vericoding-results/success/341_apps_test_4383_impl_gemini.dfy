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
function {:tailrec} ParseIntegerAccumulator(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        acc
    else if '0' <= s[i] <= '9' then
        ParseIntegerAccumulator(s, i + 1, acc * 10 + (s[i] - '0') as int)
    else
        ParseIntegerAccumulator(s, i + 1, acc)
}

function ParseIntegerHelper(s: string, i: int): int
    requires 0 <= i <= |s|
{
    ParseIntegerAccumulator(s, i, 0)
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
  if IsCelebratedAge(n) {
    result := "YES\n";
  } else {
    result := "NO\n";
  }
}
// </vc-code>

