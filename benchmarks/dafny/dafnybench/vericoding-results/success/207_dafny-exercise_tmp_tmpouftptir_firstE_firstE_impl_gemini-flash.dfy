

// <vc-helpers>
/**
 * Helper function to check if a character exists in a sequence.
 * This is not strictly necessary for the proof as Dafny's `in` operator handles it,
 * but it can be useful for conceptual clarity or if a custom check was needed.
 */
// The original `function method` syntax is deprecated, using `function` is sufficient.
// Also, this helper function is not strictly needed for verification given the `in` operator in Dafny.
// function CharInArray(c: char, a: array<char>): bool
// {
//   exists i :: 0 <= i < a.Length && a[i] == c
// }
// </vc-helpers>

// <vc-spec>
method firstE(a: array<char>) returns (x: int)
ensures if 'e' in a[..] then 0 <= x < a.Length && a[x] == 'e' && forall i | 0 <= i < x :: a[i] != 'e' else x == -1
// </vc-spec>
// <vc-code>
{
  var x_found := -1;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant (x_found == -1 && forall k | 0 <= k < i :: a[k] != 'e') ||
              (0 <= x_found < i && a[x_found] == 'e' && forall k | 0 <= k < x_found :: a[k] != 'e')
  {
    if a[i] == 'e' && x_found == -1 {
      x_found := i;
    }
    i := i + 1;
  }
  x := x_found;
}
// </vc-code>

