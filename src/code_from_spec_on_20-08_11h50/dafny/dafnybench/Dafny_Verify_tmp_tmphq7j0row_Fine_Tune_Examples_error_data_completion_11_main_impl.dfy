method main(x :int) returns (j :int, i :int)
requires x > 0
ensures j == 2 * x
// </vc-spec>
// <vc-code>
{
  j := 2 * x;
  i := 0; // i can be any value since there's no postcondition constraint on it
}
// </vc-code>