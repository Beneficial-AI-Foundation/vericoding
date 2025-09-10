predicate ValidRating(R: int) {
    0 <= R <= 4208
}

function ContestForRating(R: int): string {
    if R < 1200 then "ABC\n"
    else if R < 2800 then "ARC\n" 
    else "AGC\n"
}

// <vc-helpers>
lemma LemmaContestForRating(R: int)
    requires ValidRating(R)
    ensures R < 1200 ==> ContestForRating(R) == "ABC\n"
    ensures 1200 <= R < 2800 ==> ContestForRating(R) == "ARC\n"
    ensures R >= 2800 ==> ContestForRating(R) == "AGC\n"
{
    // The ContestForRating function is defined directly, so its properties
    // like these implications are self-evident from its definition.
    // No specific proof steps are typically needed for simple branches like this,
    // as Dafny's reasoning engine can often infer them directly.
}
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
    var r_string: string;
    if R < 1200 {
        r_string := "ABC\n";
    } else if R < 2800 {
        r_string := "ARC\n";
    } else {
        r_string := "AGC\n";
    }
    result := r_string;

    // Use the lemma to link the result to ContestForRating
    LemmaContestForRating(R);
}
// </vc-code>

