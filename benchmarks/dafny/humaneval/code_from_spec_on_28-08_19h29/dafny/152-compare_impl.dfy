// <vc-helpers>
// Helper function for absolute difference
function abs_diff(a: real, b: real): real
    ensures abs_diff(a, b) >= 0.0
{
    if a >= b then a - b else b - a
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def compare(scores: List float, guesses: List float) -> List [float]
I think we all remember that feeling when the result of some long-awaited event is finally known. The feelings and thoughts you have at that moment are definitely worth noting down and comparing. Your task is to determine if a person correctly guessed the results of a number of matches. You are given two arrays of scores and guesses of equal length, where each index shows a match. Return an array of the same length denoting how far off each guess was. If they have guessed correctly, the value is 0, and if not, the value is the absolute difference between the guess and the score.
*/
// </vc-description>

// <vc-spec>
method Compare(scores: seq<real>, guesses: seq<real>) returns (differences: seq<real>)
    requires |scores| == |guesses|
    ensures |differences| == |scores|
    ensures forall i :: 0 <= i < |scores| ==> differences[i] == abs_diff(scores[i], guesses[i])
// </vc-spec>
// <vc-code>
{
    var result: seq<real> := [];
    for i := 0 to |scores|
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> result[k] == abs_diff(scores[k], guesses[k])
    {
        result := result + [abs_diff(scores[i], guesses[i])];
    }
    return result;
}
// </vc-code>

function abs(x: int): int
    ensures 0 <= abs(x)
{
  if x < 0 then -x else x
}
// pure-end