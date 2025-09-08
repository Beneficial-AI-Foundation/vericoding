Given N apple trees numbered 1 to N in a row, find the minimum number of inspectors
needed to inspect all trees. Each inspector at position i covers trees from (i-D) to (i+D).

predicate ValidInput(N: int, D: int)
{
  N >= 1 && N <= 20 && D >= 1 && D <= 20
}

function CoverageRange(position: int, D: int): (int, int)
{
  (position - D, position + D)
}

predicate TreesCovered(N: int, D: int, inspectors: int)
{
  inspectors >= 1 && inspectors <= N && inspectors == ((N - 1) / (2 * D + 1)) + 1
}
