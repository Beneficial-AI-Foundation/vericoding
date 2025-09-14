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

// </vc-helpers>

// <vc-spec>
method solve(A: string, B: string, C: string) returns (result: char)
    requires ValidInput(A, B, C)
    ensures ValidWinner(result)
// </vc-spec>
// <vc-code>
{
  var pa: nat := 0;
  var pb: nat := 0;
  var pc: nat := 0;
  var turn: char := 'A';
  
  while true
    decreases (|A| - pa) + (|B| - pb) + (|C| - pc)
    invariant 0 <= pa <= |A| && 0 <= pb <= |B| && 0 <= pc <= |C|
    invariant turn == 'A' || turn == 'B' || turn == 'C'
  {
    if turn == 'A' {
      if pa == |A| {
        result := 'A';
        return;
      }
      var card := A[pa];
      pa := pa + 1;
      if card == 'a' { turn := 'A'; }
      else if card == 'b' { turn := 'B'; }
      else { turn := 'C'; }
    } else if turn == 'B' {
      if pb == |B| {
        result := 'B';
        return;
      }
      var card := B[pb];
      pb := pb + 1;
      if card == 'a' { turn := 'A'; }
      else if card == 'b' { turn := 'B'; }
      else { turn := 'C'; }
    } else { // turn == 'C'
      if pc == |C| {
        result := 'C';
        return;
      }
      var card := C[pc];
      pc := pc + 1;
      if card == 'a' { turn := 'A'; }
      else if card == 'b' { turn := 'B'; }
      else { turn := 'C'; }
    }
  }
}
// </vc-code>

