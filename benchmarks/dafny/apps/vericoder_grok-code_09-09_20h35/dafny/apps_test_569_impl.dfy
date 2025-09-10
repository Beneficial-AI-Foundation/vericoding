predicate ValidInput(n: int, s: string) {
    n == |s| && n >= 1
}

function CountDistinctChars(s: string): int {
    |set c | c in s|
}

// <vc-helpers>
// No updates needed in helpers
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: int)
    requires ValidInput(n, s)
    ensures n > 26 ==> result == -1
    ensures n <= 26 ==> result >= 0 && result < n
    ensures n <= 26 ==> result == |s| - CountDistinctChars(s)
// </vc-spec>
// <vc-code>
{
  if n > 26 {
    return -1;
  } else {
    var distinct: set<char> := {};
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant distinct == set c | c in s[..i]
    {
      distinct := distinct + {s[i]};
      i := i + 1;
    }
    return n - |distinct|; 
  }
}
// </vc-code>

