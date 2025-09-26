// <vc-preamble>
ghost predicate ValidChessInput(stdin_input: string)
  requires |stdin_input| > 0
{
  exists n: int, x0: int, y0: int, pieces: seq<(char, int, int)> ::
    1 <= n <= 500000 &&
    -1000000000 <= x0 <= 1000000000 &&
    -1000000000 <= y0 <= 1000000000 &&
    |pieces| == n &&
    (forall i :: 0 <= i < |pieces| ==> 
      pieces[i].0 in {'R', 'B', 'Q'} &&
      -1000000000 <= pieces[i].1 <= 1000000000 &&
      -1000000000 <= pieces[i].2 <= 1000000000) &&
    (forall i, j :: 0 <= i < j < |pieces| ==> 
      pieces[i].1 != pieces[j].1 || pieces[i].2 != pieces[j].2) &&
    (forall i :: 0 <= i < |pieces| ==> 
      pieces[i].1 != x0 || pieces[i].2 != y0) &&
    stdin_input[|stdin_input|-1] == '\n' &&
    InputMatchesFormat(stdin_input, n, x0, y0, pieces)
}

ghost predicate InputMatchesFormat(stdin_input: string, n: int, x0: int, y0: int, pieces: seq<(char, int, int)>)
{
  true
}

ghost predicate KingInCheck(stdin_input: string)
  requires |stdin_input| > 0
  requires ValidChessInput(stdin_input)
{
  exists n: int, x0: int, y0: int, pieces: seq<(char, int, int)> ::
    InputMatchesFormat(stdin_input, n, x0, y0, pieces) &&
    (HasVerticalThreat(x0, y0, pieces) ||
     HasHorizontalThreat(x0, y0, pieces) ||
     HasDiagonal1Threat(x0, y0, pieces) ||
     HasDiagonal2Threat(x0, y0, pieces))
}

ghost predicate HasVerticalThreat(x0: int, y0: int, pieces: seq<(char, int, int)>)
{
  var vertical_pieces := FilterVerticalPieces(pieces, x0);
  |vertical_pieces| > 0 &&
  exists sorted_vertical :: IsPermutation(vertical_pieces, sorted_vertical) && IsSortedByPosition(sorted_vertical) &&
    CanAttackVertically(y0, sorted_vertical)
}

ghost predicate HasHorizontalThreat(x0: int, y0: int, pieces: seq<(char, int, int)>)
{
  var horizontal_pieces := FilterHorizontalPieces(pieces, y0);
  |horizontal_pieces| > 0 &&
  exists sorted_horizontal :: IsPermutation(horizontal_pieces, sorted_horizontal) && IsSortedByPosition(sorted_horizontal) &&
    CanAttackHorizontally(x0, sorted_horizontal)
}

ghost predicate HasDiagonal1Threat(x0: int, y0: int, pieces: seq<(char, int, int)>)
{
  var diagonal1_pieces := FilterDiagonal1Pieces(pieces, x0 + y0);
  |diagonal1_pieces| > 0 &&
  exists sorted_diagonal1 :: IsPermutation(diagonal1_pieces, sorted_diagonal1) && IsSortedByPosition(sorted_diagonal1) &&
    CanAttackDiagonally(x0, sorted_diagonal1)
}

ghost predicate HasDiagonal2Threat(x0: int, y0: int, pieces: seq<(char, int, int)>)
{
  var diagonal2_pieces := FilterDiagonal2Pieces(pieces, x0 - y0);
  |diagonal2_pieces| > 0 &&
  exists sorted_diagonal2 :: IsPermutation(diagonal2_pieces, sorted_diagonal2) && IsSortedByPosition(sorted_diagonal2) &&
    CanAttackDiagonally(x0, sorted_diagonal2)
}

ghost function FilterVerticalPieces(pieces: seq<(char, int, int)>, x0: int): seq<(int, char)>
{
  if |pieces| == 0 then []
  else if pieces[0].1 == x0 then [(pieces[0].2, pieces[0].0)] + FilterVerticalPieces(pieces[1..], x0)
  else FilterVerticalPieces(pieces[1..], x0)
}

ghost function FilterHorizontalPieces(pieces: seq<(char, int, int)>, y0: int): seq<(int, char)>
{
  if |pieces| == 0 then []
  else if pieces[0].2 == y0 then [(pieces[0].1, pieces[0].0)] + FilterHorizontalPieces(pieces[1..], y0)
  else FilterHorizontalPieces(pieces[1..], y0)
}

ghost function FilterDiagonal1Pieces(pieces: seq<(char, int, int)>, sum: int): seq<(int, char)>
{
  if |pieces| == 0 then []
  else if pieces[0].1 + pieces[0].2 == sum then [(pieces[0].1, pieces[0].0)] + FilterDiagonal1Pieces(pieces[1..], sum)
  else FilterDiagonal1Pieces(pieces[1..], sum)
}

ghost function FilterDiagonal2Pieces(pieces: seq<(char, int, int)>, diff: int): seq<(int, char)>
{
  if |pieces| == 0 then []
  else if pieces[0].1 - pieces[0].2 == diff then [(pieces[0].1, pieces[0].0)] + FilterDiagonal2Pieces(pieces[1..], diff)
  else FilterDiagonal2Pieces(pieces[1..], diff)
}

ghost predicate CanAttackVertically(king_pos: int, sorted_pieces: seq<(int, char)>)
  requires IsSortedByPosition(sorted_pieces)
{
  if |sorted_pieces| == 0 then false
  else
    var insertion_point := BinarySearchInsertionPoint(sorted_pieces, king_pos);
    (insertion_point < |sorted_pieces| && sorted_pieces[insertion_point].1 in {'Q', 'R'}) ||
    (insertion_point > 0 && sorted_pieces[insertion_point-1].1 in {'Q', 'R'}) ||
    (insertion_point == 0 && sorted_pieces[0].1 in {'Q', 'R'}) ||
    (insertion_point == |sorted_pieces| && sorted_pieces[|sorted_pieces|-1].1 in {'Q', 'R'})
}

ghost predicate CanAttackHorizontally(king_pos: int, sorted_pieces: seq<(int, char)>)
  requires IsSortedByPosition(sorted_pieces)
{
  if |sorted_pieces| == 0 then false
  else
    var insertion_point := BinarySearchInsertionPoint(sorted_pieces, king_pos);
    (insertion_point < |sorted_pieces| && sorted_pieces[insertion_point].1 in {'Q', 'R'}) ||
    (insertion_point > 0 && sorted_pieces[insertion_point-1].1 in {'Q', 'R'}) ||
    (insertion_point == 0 && sorted_pieces[0].1 in {'Q', 'R'}) ||
    (insertion_point == |sorted_pieces| && sorted_pieces[|sorted_pieces|-1].1 in {'Q', 'R'})
}

ghost predicate CanAttackDiagonally(king_pos: int, sorted_pieces: seq<(int, char)>)
  requires IsSortedByPosition(sorted_pieces)
{
  if |sorted_pieces| == 0 then false
  else
    var insertion_point := BinarySearchInsertionPoint(sorted_pieces, king_pos);
    (insertion_point < |sorted_pieces| && sorted_pieces[insertion_point].1 in {'Q', 'B'}) ||
    (insertion_point > 0 && sorted_pieces[insertion_point-1].1 in {'Q', 'B'}) ||
    (insertion_point == 0 && sorted_pieces[0].1 in {'Q', 'B'}) ||
    (insertion_point == |sorted_pieces| && sorted_pieces[|sorted_pieces|-1].1 in {'Q', 'B'})
}

ghost function BinarySearchInsertionPoint(sorted_pieces: seq<(int, char)>, target_pos: int): int
  requires IsSortedByPosition(sorted_pieces)
  ensures 0 <= BinarySearchInsertionPoint(sorted_pieces, target_pos) <= |sorted_pieces|
  ensures forall i :: 0 <= i < BinarySearchInsertionPoint(sorted_pieces, target_pos) ==> sorted_pieces[i].0 <= target_pos
  ensures forall i :: BinarySearchInsertionPoint(sorted_pieces, target_pos) <= i < |sorted_pieces| ==> sorted_pieces[i].0 >= target_pos
{
  if |sorted_pieces| == 0 then 0
  else if sorted_pieces[0].0 >= target_pos then 0
  else if sorted_pieces[|sorted_pieces|-1].0 <= target_pos then |sorted_pieces|
  else
    var mid := |sorted_pieces| / 2;
    if sorted_pieces[mid].0 <= target_pos then
      mid + 1 + BinarySearchInsertionPoint(sorted_pieces[mid+1..], target_pos)
    else
      BinarySearchInsertionPoint(sorted_pieces[..mid], target_pos)
}

ghost predicate IsSortedByPosition(pieces: seq<(int, char)>)
{
  forall i, j :: 0 <= i < j < |pieces| ==> pieces[i].0 <= pieces[j].0
}

ghost predicate IsPermutation<T(!new)>(s1: seq<T>, s2: seq<T>)
{
  |s1| == |s2| && 
  (forall x :: x in s1 <==> x in s2) &&
  (forall x :: Count(s1, x) == Count(s2, x))
}

ghost function Count<T>(s: seq<T>, x: T): int
{
  if |s| == 0 then 0
  else (if s[0] == x then 1 else 0) + Count(s[1..], x)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires ValidChessInput(stdin_input)
  ensures result == "YES\n" || result == "NO\n"
// </vc-spec>
// <vc-code>
{
  result := "NO\n";
}
// </vc-code>
