// SPEC



method mezclar(V: array?<int>, c : int, m : int, f : int)

  requires V != null
  requires c <= m <= f
  requires 0 <= c <= V.Length
  requires 0 <= m <= V.Length
  requires 0 <= f <= V.Length

  modifies V

{
}
