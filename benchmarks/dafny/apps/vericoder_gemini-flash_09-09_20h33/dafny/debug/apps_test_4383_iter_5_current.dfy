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
    // Advance 'i' past any non-digit, non-sign characters
    while i < |s| && (s[i] < '0' || s[i] > '9') && s[i] != '+' && s[i] != '-'
        invariant start <= i <= |s|
    {
        i := i + 1;
    }

    // Now 'i' is at the start of a potential number, or at the end of the string.
    // If 'i' has reached the end of the string, it means no valid number was found from 'start'.
    // Given the precondition, this branch should ideally not be taken if a digit exists.
    if i == |s| then
        0 // Should not happen given the precondition: "exists i: int :: start <= i < |s| && '0' <= s[i] <= '9'"
    else
        var sign := 1;
        var current_i := i; // Use a local variable for parsing logic

        if s[current_i] == '-' then
            sign := -1;
            current_i := current_i + 1;
        else if s[current_i] == '+' then
            current_i := current_i + 1;

        // Skip any leading non-digit characters after the sign (if any) until a digit is found
        while current_i < |s| && (s[current_i] < '0' || s[current_i] > '9')
            invariant i <= current_i <= |s|
        {
            current_i := current_i + 1;
        }

        // If we processed past a sign and landed on a non-digit, or if the original `i` was already
        // on a non-digit that we didn't explicitly check before, we might have no digits left.
        // The original precondition `exists i: int :: start <= i < |s| && '0' <= s[i] <= '9'`
        // guarantees there is *some* digit in the string.
        // We need to ensure that after skipping non-digits and signs, we still have digits.
        if current_i == |s| || s[current_i] < '0' || s[current_i] > '9' then
            // This case should ideally be covered by the precondition if `ParseIntegerValue` is called correctly.
            // However, within `ParseIntegerHelper`'s local parsing, we might reach here if
            // the initial `start` was beyond the actual digits or if the digits were at the
            // very beginning and we skipped past them with non-digit/sign characters.
            // As a fallback, return 0 if no digits are found after processing signs/non-digits.
            0
        else
            var value := 0;
            var j := current_i; // Start parsing digits from 'current_i'
            while j < |s| && '0' <= s[j] <= '9'
                invariant current_i <= j <= |s|
                invariant value >= 0
                invariant forall k :: current_i <= k < j ==> '0' <= s[k] <= '9'
                invariant (value == 0 && j == current_i) || (value > 0) || (s[current_i] == '0' && j > current_i)
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

