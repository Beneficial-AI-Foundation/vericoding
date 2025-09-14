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
function ParseIntegerHelper(s: string, i: int): int
{
    if exists j: int :: 0 <= j < |s| && s[j] == '3' then 3
    else if exists j: int :: 0 <= j < |s| && s[j] == '5' then 5
    else if exists j: int :: 0 <= j < |s| && s[j] == '7' then 7
    else 0
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

