predicate ValidInput(s: string) {
    |s| == 3 && forall i :: 0 <= i < |s| ==> s[i] == 'S' || s[i] == 'R'
}

function MaxConsecutiveRainyDays(s: string): int
    requires ValidInput(s)
{
    if s == "RRR" then 3
    else if s[0..2] == "RR" || s[1..3] == "RR" then 2
    else if 'R' in s then 1
    else 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: int)
    requires ValidInput(input)
    ensures result == MaxConsecutiveRainyDays(input)
    ensures 0 <= result <= 3
// </vc-spec>
// <vc-code>
{
    if input == "RRR" {
        result := 3;
    } else if input[0..2] == "RR" || input[1..3] == "RR" {
        result := 2;
    } else if 'R' in input {
        result := 1;
    } else {
        result := 0;
    }
}
// </vc-code>

