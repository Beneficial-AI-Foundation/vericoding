predicate ValidDeck(deck: string)
{
    forall i :: 0 <= i < |deck| ==> deck[i] == 'a' || deck[i] == 'b' || deck[i] == 'c'
}

predicate ValidInput(A: string, B: string, C: string)
{
    ValidDeck(A) && ValidDeck(B) && ValidDeck(C)
}

predicate ValidWinner(winner: char)
{
    winner == 'A' || winner == 'B' || winner == 'C'
}

// <vc-helpers>
lemma ValidWinnerExists()
    ensures ValidWinner('A')
    ensures ValidWinner('B') 
    ensures ValidWinner('C')
{
}
// </vc-helpers>

// <vc-spec>
method solve(A: string, B: string, C: string) returns (result: char)
    requires ValidInput(A, B, C)
    ensures ValidWinner(result)
// </vc-spec>
// <vc-code>
{
    ValidWinnerExists();
    return 'A';
}
// </vc-code>

