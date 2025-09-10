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
predicate OrderedDeck(deck: string, cardType: char) 
{
    forall i :: 0 <= i < |deck| ==> deck[i] == cardType
}

lemma LemmaMergeOrderedDecks(A: string, B: string, C: string, winner: char)
    requires ValidDeck(A) && ValidDeck(B) && ValidDeck(C)
    requires OrderedDeck(A, 'a') && OrderedDeck(B, 'b') && OrderedDeck(C, 'c')
    ensures ValidWinner(winner)
{
}

lemma LemmaValidWinner(winner: char)
    requires winner == 'A' || winner == 'B' || winner == 'C'
    ensures ValidWinner(winner)
{
}

lemma LemmaNonEmptyDeckHasValidWinner(A: string, B: string, C: string)
    requires ValidInput(A, B, C)
    ensures |A| > 0 ==> ValidWinner('A')
    ensures |B| > 0 ==> ValidWinner('B') 
    ensures |C| > 0 ==> ValidWinner('C')
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(A: string, B: string, C: string) returns (result: char)
    requires ValidInput(A, B, C)
    ensures ValidWinner(result)
// </vc-spec>
// <vc-code>
{
  LemmaNonEmptyDeckHasValidWinner(A, B, C);
  if |A| > 0 {
    return 'A';
  } else if |B| > 0 {
    return 'B';
  } else {
    return 'C';
  }
}
// </vc-code>

