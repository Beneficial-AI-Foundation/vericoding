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
function ParseIntegerHelper(s: string, start: int): int
    requires start < |s|
    requires exists i: int :: start <= i < |s| && '0' <= s[i] <= '9'
    decreases |s| - start
{
    var i := start;
     while i < |s| && (s[i] < '0' || s[i] > '9') && s[i] != '+' && s[i] != '-'
    invariant i <= |s|
    invariant start <= i
    {
        i := i + 1;
    }
    if i == |s| then
        0 // Should not happen given the precondition
    else
        var sign := 1;
        if s[i] == '-' then
            sign := -1;
            i := i + 1;
        else if s[i] == '+' then
            i := i + 1;

        var value := 0;
        var j := i;
        while j < |s| && '0' <= s[j] <= '9'
            invariant i <= j <= |s|
            invariant value >= 0
            invariant forall k :: i <= k < j ==> '0' <= s[k] <= '9'
        {
            value := value * 10 + (s[j] - '0');
            j := j + 1;
        }
        sign * value
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
  if IsCelebratedAge(n) then
    result := "YES\n";
  else
    result := "NO\n";
  return result;
}
// </vc-code>

