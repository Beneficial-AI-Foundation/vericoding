predicate ValidInput(position: string)
{
  |position| == 2 && 'a' <= position[0] <= 'h' && '1' <= position[1] <= '8'
}

predicate IsCorner(position: string)
  requires ValidInput(position)
{
  (position[0] == 'a' || position[0] == 'h') && (position[1] == '1' || position[1] == '8')
}

predicate IsEdge(position: string)
  requires ValidInput(position)
{
  (position[0] == 'a' || position[0] == 'h' || position[1] == '1' || position[1] == '8') && !IsCorner(position)
}

predicate IsInterior(position: string)
  requires ValidInput(position)
{
  !IsCorner(position) && !IsEdge(position)
}

function ValidMoves(position: string): int
  requires ValidInput(position)
{
  if IsCorner(position) then 3
  else if IsEdge(position) then 5
  else 8
}

// <vc-helpers>
lemma CornerEdgeInteriorPartition(position: string)
  requires ValidInput(position)
  ensures IsCorner(position) || IsEdge(position) || IsInterior(position)
{
}

lemma CornerEdgeDisjoint(position: string)
  requires ValidInput(position)
  ensures !(IsCorner(position) && IsEdge(position))
{
}

lemma ValidMovesCorner(position: string)
  requires ValidInput(position) && IsCorner(position)
  ensures ValidMoves(position) == 3
{
}

lemma ValidMovesEdge(position: string)
  requires ValidInput(position) && IsEdge(position)
  ensures ValidMoves(position) == 5
{
}

lemma ValidMovesInterior(position: string)
  requires ValidInput(position) && IsInterior(position)
  ensures ValidMoves(position) == 8
{
}
// </vc-helpers>

// <vc-spec>
method solve(position: string) returns (moves: int)
  requires ValidInput(position)
  ensures moves == ValidMoves(position)
  ensures IsCorner(position) ==> moves == 3
  ensures IsEdge(position) ==> moves == 5
  ensures IsInterior(position) ==> moves == 8
  ensures moves == 3 || moves == 5 || moves == 8
// </vc-spec>
// <vc-code>
{
  CornerEdgeInteriorPartition(position);
  if IsCorner(position) {
    ValidMovesCorner(position);
    moves := 3;
  } else if IsEdge(position) {
    ValidMovesEdge(position);
    moves := 5;
  } else {
    ValidMovesInterior(position);
    moves := 8;
  }
}
// </vc-code>

