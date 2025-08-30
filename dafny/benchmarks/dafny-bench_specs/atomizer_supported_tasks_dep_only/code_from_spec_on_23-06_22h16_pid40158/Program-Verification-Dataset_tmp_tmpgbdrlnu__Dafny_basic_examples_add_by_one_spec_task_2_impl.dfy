//ATOM_PLACEHOLDER_add_by_one



























































/*
 * Illustrates de-sugaring of the while loop.
*/
//IMPL bar
method bar (x:int, y:int) returns (r:int)
  requires y >= 0;
  ensures r == x + y;
{
  r := x + y;
}