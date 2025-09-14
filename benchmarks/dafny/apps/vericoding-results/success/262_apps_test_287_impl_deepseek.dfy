predicate ValidInput(n: int, k: int)
{
    n >= 1 && k >= 0 && k <= n
}

predicate ValidOutput(result: seq<int>, n: int, k: int)
{
    |result| == 2 && 
    result[0] >= 0 && 
    result[1] >= 0 && 
    result[0] <= result[1] &&
    result[0] <= n - k &&
    result[1] <= n - k
}

function MinGoodApartments(n: int, k: int): int
    requires ValidInput(n, k)
{
    if k == 0 || k == n then 0 else 1
}

function MaxGoodApartments(n: int, k: int): int
    requires ValidInput(n, k)
{
    if k == 0 || k == n then 0
    else if n - k < k * 2 then n - k
    else k * 2
}

// <vc-helpers>
lemma MinGoodApartmentsLemma(n: int, k: int)
    requires ValidInput(n, k)
    ensures MinGoodApartments(n, k) == 0 || MinGoodApartments(n, k) == 1
{
}

lemma MaxGoodApartmentsLemma(n: int, k: int)
    requires ValidInput(n, k)
    ensures MaxGoodApartments(n, k) >= 0 && MaxGoodApartments(n, k) <= 2 * k && MaxGoodApartments(n, k) <= n - k
{
}

lemma ValidOutputLemma(n: int, k: int, result: seq<int>)
    requires ValidInput(n, k)
    requires |result| == 2 && result[0] == MinGoodApartments(n, k) && result[1] == MaxGoodApartments(n, k)
    ensures ValidOutput(result, n, k)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures ValidOutput(result, n, k)
    ensures result[0] == MinGoodApartments(n, k)
    ensures result[1] == MaxGoodApartments(n, k)
// </vc-spec>
// <vc-code>
{
  var min := MinGoodApartments(n, k);
  var max := MaxGoodApartments(n, k);
  result := [min, max];
  ValidOutputLemma(n, k, result);
}
// </vc-code>

