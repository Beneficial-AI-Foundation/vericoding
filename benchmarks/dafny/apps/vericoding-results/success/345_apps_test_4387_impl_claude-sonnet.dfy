predicate ValidRating(R: int) {
    0 <= R <= 4208
}

function ContestForRating(R: int): string {
    if R < 1200 then "ABC\n"
    else if R < 2800 then "ARC\n" 
    else "AGC\n"
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(R: int) returns (result: string)
    requires ValidRating(R)
    ensures result == ContestForRating(R)
    ensures R < 1200 ==> result == "ABC\n"
    ensures 1200 <= R < 2800 ==> result == "ARC\n"
    ensures R >= 2800 ==> result == "AGC\n"
// </vc-spec>
// <vc-code>
{
    if R < 1200 {
        result := "ABC\n";
    } else if R < 2800 {
        result := "ARC\n";
    } else {
        result := "AGC\n";
    }
}
// </vc-code>

