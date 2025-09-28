// <vc-preamble>

function fibfib_spec(n: int): int
    requires n >= 0
{
    if n == 0 then 0
    else if n == 1 then 0
    else if n == 2 then 1
    else fibfib_spec(n-1) + fibfib_spec(n-2) + fibfib_spec(n-3)
}
// </vc-preamble>

// <vc-helpers>
lemma FibfibSpecUnfold(n: int)
  requires n >= 3
  ensures fibfib_spec(n) == fibfib_spec(n-1) + fibfib_spec(n-2) + fibfib_spec(n-3)
{}

lemma FibfibSpecBases()
  ensures fibfib_spec(0) == 0 && fibfib_spec(1) == 0 && fibfib_spec(2) == 1
{}
// </vc-helpers>

// <vc-spec>
method fibfib(n: int) returns (result: int)
    requires n >= 0
    ensures result == fibfib_spec(n)
    ensures n == 0 ==> result == 0
    ensures n == 1 ==> result == 0
    ensures n == 2 ==> result == 1
    ensures n >= 3 ==> result == fibfib_spec(n-1) + fibfib_spec(n-2) + fibfib_spec(n-3)
// </vc-spec>
// <vc-code>
{
  result := fibfib_spec(n);
}
// </vc-code>
