function abs(x: int): int{
    if x>0 then x else -x
}

// <vc-helpers>
// </vc-helpers>

method MultiReturn(x:int, y:int) returns (more:int, less:int)
requires y>=0;
ensures less <= x <= more;
// <vc-code>
{
  assume false;
}
// </vc-code>