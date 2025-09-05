// ======= TASK =======
// Given a password string, determine if it meets complexity requirements.
// A password is complex enough if it satisfies ALL conditions:
// - Length is at least 5 characters
// - Contains at least one uppercase English letter (A-Z)
// - Contains at least one lowercase English letter (a-z)
// - Contains at least one digit (0-9)
// Output "Correct" if requirements met, otherwise "Too weak".

// ======= SPEC REQUIREMENTS =======
function stripWhitespace(s: string): string
{
    var s1 := stripTrailing(s);
    stripLeading(s1)
}

predicate hasLowercase(s: string)
{
    exists i :: 0 <= i < |s| && 'a' <= s[i] <= 'z'
}

predicate hasUppercase(s: string)
{
    exists i :: 0 <= i < |s| && 'A' <= s[i] <= 'Z'
}

predicate hasDigit(s: string)
{
    exists i :: 0 <= i < |s| && '0' <= s[i] <= '9'
}

predicate ValidPassword(s: string)
{
    var cleaned := stripWhitespace(s);
    |cleaned| >= 5 && hasLowercase(cleaned) && hasUppercase(cleaned) && hasDigit(cleaned)
}

// <vc-helpers>
function stripTrailing(s: string): string
{
    if |s| == 0 then s
    else if s[|s|-1] == ' ' || s[|s|-1] == '\n' || s[|s|-1] == '\r' then stripTrailing(s[..|s|-1])
    else s
}

function stripLeading(s: string): string
{
    if |s| == 0 then s
    else if s[0] == ' ' || s[0] == '\n' || s[0] == '\r' then stripLeading(s[1..])
    else s
}

lemma LoopInvariantPreservation(s: string, i: int, flag2: bool, flag3: bool, flag4: bool)
    requires 0 <= i < |s|
    requires flag2 <==> (exists j :: 0 <= j < i && 'a' <= s[j] <= 'z')
    requires flag3 <==> (exists j :: 0 <= j < i && 'A' <= s[j] <= 'Z')
    requires flag4 <==> (exists j :: 0 <= j < i && '0' <= s[j] <= '9')
    ensures (flag2 || ('a' <= s[i] <= 'z')) <==> (exists j :: 0 <= j < i+1 && 'a' <= s[j] <= 'z')
    ensures (flag3 || ('A' <= s[i] <= 'Z')) <==> (exists j :: 0 <= j < i+1 && 'A' <= s[j] <= 'Z')
    ensures (flag4 || ('0' <= s[i] <= '9')) <==> (exists j :: 0 <= j < i+1 && '0' <= s[j] <= '9')
{
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    ensures ValidPassword(input) ==> output == "Correct"
    ensures !ValidPassword(input) ==> output == "Too weak"
// </vc-spec>
// <vc-code>
{
    var s := stripWhitespace(input);

    var flag1 := |s| >= 5;

    var flag2 := false;
    var flag3 := false;
    var flag4 := false;

    for i := 0 to |s|
        invariant flag2 <==> (exists j :: 0 <= j < i && 'a' <= s[j] <= 'z')
        invariant flag3 <==> (exists j :: 0 <= j < i && 'A' <= s[j] <= 'Z')
        invariant flag4 <==> (exists j :: 0 <= j < i && '0' <= s[j] <= '9')
    {
        var c := s[i];
        
        LoopInvariantPreservation(s, i, flag2, flag3, flag4);
        
        if 'a' <= c <= 'z' {
            flag2 := true;
        }
        if 'A' <= c <= 'Z' {
            flag3 := true;
        }
        if '0' <= c <= '9' {
            flag4 := true;
        }
    }

    if flag1 && flag2 && flag3 && flag4 {
        output := "Correct";
    } else {
        output := "Too weak";
    }
}
// </vc-code>

