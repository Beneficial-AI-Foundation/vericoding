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
function ord(c: char): int
{
    int(c)
}

function pow10(n: int): int
    requires n >= 0
    decreases n
{
    if n == 0 then 1 else 10 * pow10(n - 1)
}

function ParseDigits(s: string, i: int): (int, int)
    requires 0 <= i < |s|
    decreases |s| - i
{
    if !('0' <= s[i] <= '9') then (0, 0)
    else if i + 1 >= |s| || !('0' <= s[i + 1] <= '9') then (ord(s[i]) - ord('0'), 1)
    else
        var tail := ParseDigits(s, i + 1);
        var tailVal := tail.0;
        var tailLen := tail.1;
        ((ord(s[i]) - ord('0')) * pow10(tailLen) + tailVal, tailLen + 1)
}

function ParseIntegerHelper(s: string, i: int): int
    requires |s| > 0
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then 0
    else if '0' <= s[i] <= '9' then
        var p := ParseDigits(s, i);
        p.0
    else ParseIntegerHelper(s, i + 1)
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

