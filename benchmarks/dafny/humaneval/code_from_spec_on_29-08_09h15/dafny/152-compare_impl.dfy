

// <vc-helpers>
lemma AbsProperties(x: int, y: int)
    ensures abs(x - y) == abs(y - x)
    ensures abs(x - y) >= 0
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def compare(scores: List float, guesses: List float) -> List [float]
I think we all remember that feeling when the result of some long-awaited event is finally known. The feelings and thoughts you have at that moment are definitely worth noting down and comparing. Your task is to determine if a person correctly guessed the results of a number of matches. You are given two arrays of scores and guesses of equal length, where each index shows a match. Return an array of the same length denoting how far off each guess was. If they have guessed correctly, the value is 0, and if not, the value is the absolute difference between the guess and the score.
*/
// </vc-description>

// <vc-spec>
method Compare(scores: array<int>, guesses: array<int>) returns (result: array<int>)
  // pre-conditions-start
  requires scores.Length == guesses.Length
  // pre-conditions-end
  // post-conditions-start
  ensures result.Length == scores.Length
  ensures forall i :: 0 <= i < result.Length ==> result[i] == abs(scores[i] - guesses[i])
  // post-conditions-end
// </vc-spec>

// <vc-code>
{
    result := new int[scores.Length];
    
    var i := 0;
    while i < scores.Length
        invariant 0 <= i <= scores.Length
        invariant result.Length == scores.Length
        invariant forall j :: 0 <= j < i ==> result[j] == abs(scores[j] - guesses[j])
    {
        result[i] := abs(scores[i] - guesses[i]);
        i := i + 1;
    }
}
// </vc-code>

function abs(x: int): int
    ensures 0 <= abs(x)
{
  if x < 0 then -x else x
}
// pure-end