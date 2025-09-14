predicate ValidInput(a: int) {
    1 <= a <= 40
}

function Presidents(): seq<string> {
    [
        "Washington", "Adams", "Jefferson", "Madison", "Monroe", "Adams", "Jackson", 
        "Van Buren", "Harrison", "Tyler", "Polk", "Taylor", "Fillmore", "Pierce", 
        "Buchanan", "Lincoln", "Johnson", "Grant", "Hayes", "Garfield", "Arthur", 
        "Cleveland", "Harrison", "Cleveland", "McKinley", "Roosevelt", "Taft", 
        "Wilson", "Harding", "Coolidge", "Hoover", "Roosevelt", "Truman", 
        "Eisenhower", "Kennedy", "Johnson", "Nixon", "Ford", "Carter", "Reagan"
    ]
}

// <vc-helpers>
lemma PresidentsIndexValid(a: int)
    requires ValidInput(a)
    ensures 0 <= a-1 < |Presidents()|
{
}
// </vc-helpers>

// <vc-spec>
method solve(a: int) returns (result: string)
    requires ValidInput(a)
    ensures result == Presidents()[a - 1]
// </vc-spec>
// <vc-code>
{
    PresidentsIndexValid(a);
    result := Presidents()[a - 1];
}
// </vc-code>

