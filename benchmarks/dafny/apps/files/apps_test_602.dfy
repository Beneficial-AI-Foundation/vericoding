Given an integer a (1 ≤ a ≤ 40), output the last name of the a-th President of the United States.

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

method solve(a: int) returns (result: string)
    requires ValidInput(a)
    ensures result == Presidents()[a - 1]
{
    var presidents := Presidents();
    result := presidents[a - 1];
}
