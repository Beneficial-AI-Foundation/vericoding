predicate ValidInput(a: int, b: int)
{
  a >= 1 && b > a && b < 499500
}

predicate ValidSnowDepth(a: int, b: int, depth: int)
{
  depth >= 1 &&
  ((b - a) * (b - a) - (a + b)) >= 2 &&
  ((b - a) * (b - a) - (a + b)) % 2 == 0
}

function SnowDepthFormula(a: int, b: int): int
  requires ValidInput(a, b)
  requires ValidSnowDepth(a, b, ((b - a) * (b - a) - (a + b)) / 2)
{
  ((b - a) * (b - a) - (a + b)) / 2
}

// <vc-helpers>
/**
 * Since SnowDepthFormula is a function, its purity is guaranteed by Dafny.
 * The 'requires' clauses of SnowDepthFormula already involve ValidInput and ValidSnowDepth.
 * Therefore, no explicit helper predicates or lemmas are strictly necessary beyond what's provided for the helpers.
 * The core logic simply involves directly computing the formula.
 */
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
  requires ValidInput(a, b)
  requires ValidSnowDepth(a, b, ((b - a) * (b - a) - (a + b)) / 2)
  ensures result >= 1
  ensures result == SnowDepthFormula(a, b)
// </vc-spec>
// <vc-code>
{
  var depth := ((b - a) * (b - a) - (a + b)) / 2;
  return depth;
}
// </vc-code>

