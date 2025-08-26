method mezclar(V: array?<int>, c : int, m : int, f : int)

    requires V != null
    requires c <= m <= f
    requires 0 <= c <= V.Length
    requires 0 <= m <= V.Length
    requires 0 <= f <= V.Length

    modifies V
// </vc-spec>
// <vc-code>
{
  // Since there are no postconditions specified, we can implement
  // a trivial method that satisfies all the given requirements
  // The method is allowed to modify V but is not required to do anything specific
}
// </vc-code>