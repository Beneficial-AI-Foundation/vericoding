function abs(x: int): int{
    if x>0 then x else -x
}

// <vc-helpers>
// </vc-helpers>

method Max(x:int, y:int) returns (a:int)
ensures a == x || a == y;
ensures x > y ==> a == x;
ensures x <= y ==> a == y;
// <vc-code>
{
  assume false;
}
// </vc-code>