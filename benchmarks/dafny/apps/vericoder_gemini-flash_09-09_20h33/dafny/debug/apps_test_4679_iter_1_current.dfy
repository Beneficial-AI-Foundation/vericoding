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
function getCounts(s: string): map<char, int>
  reads s
  ensures forall c :: c in 'a'..'c' || c == 'a' || c == 'b' || c == 'c' ==> getCounts(s)[c] == countChar(s, c)
{
  var counts := map<char, int>[];
  counts := counts + mapOf('a' := countChar(s, 'a'));
  counts := counts + mapOf('b' := countChar(s, 'b'));
  counts := counts + mapOf('c' := countChar(s, 'c'));
  counts
}

function countChar(s: string, c: char): int
  reads s
  decreases |s|
{
  if |s| == 0 then
    0
  else if s[0] == c then
    1 + countChar(s[1..], c)
  else
    countChar(s[1..], c)
}
// </vc-helpers>

// <vc-spec>
method solve(A: string, B: string, C: string) returns (result: char)
    requires ValidInput(A, B, C)
    ensures ValidWinner(result)
// </vc-spec>
// <vc-code>
{
    var countsA := getCounts(A);
    var countsB := getCounts(B);
    var countsC := getCounts(C);

    var scoreA := countsA['a'] + countsB['b'] + countsC['c'];
    var scoreB := countsA['b'] + countsB['c'] + countsC['a'];
    var scoreC := countsA['c'] + countsB['a'] + countsC['b'];

    if scoreA > scoreB && scoreA > scoreC then
        result := 'A';
    else if scoreB > scoreA && scoreB > scoreC then
        result := 'B';
    else
        result := 'C';
}
// </vc-code>

